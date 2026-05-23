from flask import Flask, render_template, request, jsonify, Response
from datetime import datetime
import json
import os
import math
from lxml import etree

app = Flask(__name__)

SUBJECT_PROFILES = {
    'dementia': {'avg_distance_km': 2.4, 'max_distance_km': 8.0},
    'lost_child': {'avg_distance_km': 1.6, 'max_distance_km': 4.5},
    'lost_hiker': {'avg_distance_km': 5.0, 'max_distance_km': 25.0},
    'lost_hunter': {'avg_distance_km': 4.0, 'max_distance_km': 15.0},
    'lost_vehicle': {'avg_distance_km': 10.0, 'max_distance_km': 50.0},
    'mental_health': {'avg_distance_km': 3.0, 'max_distance_km': 8.0},
}

# --- Helper functions for GPX geometry ---

def km_to_lat(km):
    """Convert kilometers to degrees of latitude."""
    return km / 111.32

def km_to_lon(km, lat):
    """Convert kilometers to degrees of longitude at a given latitude."""
    return km / (111.32 * math.cos(math.radians(lat)))

def circle_points(center_lat, center_lon, radius_km, num_points=72):
    """Generate points forming a circle around a center point."""
    points = []
    for i in range(num_points + 1):
        angle = math.radians(i * 360 / num_points)
        dlat = km_to_lat(radius_km * math.cos(angle))
        dlon = km_to_lon(radius_km * math.sin(angle), center_lat)
        points.append((center_lat + dlat, center_lon + dlon))
    return points

def sector_points(center_lat, center_lon, inner_km, outer_km, start_angle, end_angle, num_arc_points=12):
    """Generate points forming a pie-shaped sector (wedge) between two radii."""
    points = []
    if inner_km == 0:
        points.append((center_lat, center_lon))
    else:
        for i in range(num_arc_points + 1):
            angle = math.radians(start_angle + (end_angle - start_angle) * i / num_arc_points)
            dlat = km_to_lat(inner_km * math.cos(angle))
            dlon = km_to_lon(inner_km * math.sin(angle), center_lat)
            points.append((center_lat + dlat, center_lon + dlon))

    for i in range(num_arc_points + 1):
        angle = math.radians(end_angle - (end_angle - start_angle) * i / num_arc_points)
        dlat = km_to_lat(outer_km * math.cos(angle))
        dlon = km_to_lon(outer_km * math.sin(angle), center_lat)
        points.append((center_lat + dlat, center_lon + dlon))

    points.append(points[0])
    return points

def sector_area_sq_km(inner_km, outer_km, angle_degrees):
    """Calculate the area of a sector wedge in square kilometers."""
    angle_radians = math.radians(angle_degrees)
    outer_area = 0.5 * outer_km * outer_km * angle_radians
    inner_area = 0.5 * inner_km * inner_km * angle_radians
    return outer_area - inner_area

# --- GPX file builders ---

def build_rings_gpx(lat, lon, inner_km, outer_km):
    """Build a GPX file containing the inner and outer range rings as tracks."""
    nsmap = {None: 'http://www.topografix.com/GPX/1/1'}
    gpx = etree.Element('gpx', version='1.1', creator='MARLY 1.0', nsmap=nsmap)

    wpt = etree.SubElement(gpx, 'wpt', lat=str(lat), lon=str(lon))
    etree.SubElement(wpt, 'name').text = 'Last Known Position'
    etree.SubElement(wpt, 'desc').text = 'LKP - Center of search area'

    inner_trk = etree.SubElement(gpx, 'trk')
    etree.SubElement(inner_trk, 'name').text = f'Inner Ring ({inner_km} km)'
    etree.SubElement(inner_trk, 'desc').text = 'Average travel distance - Priority 1 boundary'
    inner_seg = etree.SubElement(inner_trk, 'trkseg')
    for plat, plon in circle_points(lat, lon, inner_km):
        etree.SubElement(inner_seg, 'trkpt', lat=f'{plat:.6f}', lon=f'{plon:.6f}')

    outer_trk = etree.SubElement(gpx, 'trk')
    etree.SubElement(outer_trk, 'name').text = f'Outer Ring ({outer_km} km)'
    etree.SubElement(outer_trk, 'desc').text = 'Maximum travel distance - Priority 2 boundary'
    outer_seg = etree.SubElement(outer_trk, 'trkseg')
    for plat, plon in circle_points(lat, lon, outer_km):
        etree.SubElement(outer_seg, 'trkpt', lat=f'{plat:.6f}', lon=f'{plon:.6f}')

    return etree.tostring(gpx, pretty_print=True, xml_declaration=True, encoding='UTF-8')

def build_sectors_gpx(lat, lon, inner_km, outer_km, sector_weights, max_sector_sq_km=None):
    """Build a GPX file containing the search sectors as tracks."""
    nsmap = {None: 'http://www.topografix.com/GPX/1/1'}
    gpx = etree.Element('gpx', version='1.1', creator='MARLY 1.0', nsmap=nsmap)

    wpt = etree.SubElement(gpx, 'wpt', lat=str(lat), lon=str(lon))
    etree.SubElement(wpt, 'name').text = 'Last Known Position'

    sector_names = ['N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW']
    base_angles = [0, 45, 90, 135, 180, 225, 270, 315]
    sector_span = 45  # degrees per sector
    sector_num = 1  # Sequential counter starting at 1

    # Inner sectors first (Priority 1) — get the lowest numbers
    for name, base_angle in zip(sector_names, base_angles):
        weight = sector_weights.get(name, 1.0)
        inner_area = sector_area_sq_km(0, inner_km, sector_span)

        if max_sector_sq_km and inner_area > max_sector_sq_km:
            subdivisions = math.ceil(inner_area / max_sector_sq_km)
            sub_span = sector_span / subdivisions
            for sub in range(subdivisions):
                start_angle = (base_angle - sector_span / 2) + sub * sub_span
                end_angle = start_angle + sub_span
                label = f'Sector-{sector_num:02d}'
                trk = etree.SubElement(gpx, 'trk')
                etree.SubElement(trk, 'name').text = f'{label} ({name} Wt:{weight})'
                etree.SubElement(trk, 'desc').text = f'{label} - Inner {name} - Priority 1 - Weight {weight}'
                seg = etree.SubElement(trk, 'trkseg')
                for plat, plon in sector_points(lat, lon, 0, inner_km, start_angle, end_angle):
                    etree.SubElement(seg, 'trkpt', lat=f'{plat:.6f}', lon=f'{plon:.6f}')
                sector_num += 1
        else:
            start_angle = base_angle - sector_span / 2
            end_angle = base_angle + sector_span / 2
            label = f'Sector-{sector_num:02d}'
            trk = etree.SubElement(gpx, 'trk')
            etree.SubElement(trk, 'name').text = f'{label} ({name} Wt:{weight})'
            etree.SubElement(trk, 'desc').text = f'{label} - Inner {name} - Priority 1 - Weight {weight}'
            seg = etree.SubElement(trk, 'trkseg')
            for plat, plon in sector_points(lat, lon, 0, inner_km, start_angle, end_angle):
                etree.SubElement(seg, 'trkpt', lat=f'{plat:.6f}', lon=f'{plon:.6f}')
            sector_num += 1

    # Outer sectors next (Priority 2) — restart numbering with A suffix
    outer_num = 1
    for name, base_angle in zip(sector_names, base_angles):
        weight = sector_weights.get(name, 1.0)
        outer_area = sector_area_sq_km(inner_km, outer_km, sector_span)

        if max_sector_sq_km and outer_area > max_sector_sq_km:
            subdivisions = math.ceil(outer_area / max_sector_sq_km)
            sub_span = sector_span / subdivisions
            for sub in range(subdivisions):
                start_angle = (base_angle - sector_span / 2) + sub * sub_span
                end_angle = start_angle + sub_span
                label = f'Sector-{outer_num:02d}A'
                trk = etree.SubElement(gpx, 'trk')
                etree.SubElement(trk, 'name').text = f'{label} ({name} Wt:{weight})'
                etree.SubElement(trk, 'desc').text = f'{label} - Outer {name} - Priority 2 - Weight {weight}'
                seg = etree.SubElement(trk, 'trkseg')
                for plat, plon in sector_points(lat, lon, inner_km, outer_km, start_angle, end_angle):
                    etree.SubElement(seg, 'trkpt', lat=f'{plat:.6f}', lon=f'{plon:.6f}')
                outer_num += 1
        else:
            start_angle = base_angle - sector_span / 2
            end_angle = base_angle + sector_span / 2
            label = f'Sector-{outer_num:02d}A'
            trk = etree.SubElement(gpx, 'trk')
            etree.SubElement(trk, 'name').text = f'{label} ({name} Wt:{weight})'
            etree.SubElement(trk, 'desc').text = f'{label} - Outer {name} - Priority 2 - Weight {weight}'
            seg = etree.SubElement(trk, 'trkseg')
            for plat, plon in sector_points(lat, lon, inner_km, outer_km, start_angle, end_angle):
                etree.SubElement(seg, 'trkpt', lat=f'{plat:.6f}', lon=f'{plon:.6f}')
            outer_num += 1

    return etree.tostring(gpx, pretty_print=True, xml_declaration=True, encoding='UTF-8')

# --- Routes ---

@app.route('/')
def index():
    return render_template('form.html')

@app.route('/submit', methods=['POST'])
def submit_form():
    data = request.json
    search_plan = {
        'timestamp': datetime.now().isoformat(),
        'subject_type': data.get('subject_type'),
        'latitude': data.get('latitude'),
        'longitude': data.get('longitude'),
        'time_last_seen': data.get('time_last_seen'),
        'age': data.get('age'),
        'terrain': data.get('terrain'),
        'notes': data.get('notes'),
    }
    with open('search_plans.json', 'a') as f:
        f.write(json.dumps(search_plan) + '\n')
    return jsonify({'success': True})

@app.route('/generate-search-plan', methods=['POST'])
def generate_search_plan():
    data = request.json
    subject_type = data.get('subject_type')
    latitude = float(data.get('latitude'))
    longitude = float(data.get('longitude'))
    notes = data.get('notes', '')

    # Search parameters from Step 2
    params = data.get('search_params', {})
    custom_inner = params.get('custom_inner_radius')
    custom_outer = params.get('custom_outer_radius')
    max_sector_sq_km = params.get('max_sector_sq_km')
    num_teams = params.get('num_teams')
    team_capability = params.get('team_capability')
    urgency_hours = params.get('urgency_hours')

    zones = calculate_search_zones(
        latitude, longitude, subject_type, notes,
        custom_inner=custom_inner,
        custom_outer=custom_outer,
        max_sector_sq_km=max_sector_sq_km,
        num_teams=num_teams,
        team_capability=team_capability,
        urgency_hours=urgency_hours,
    )
    return jsonify({'success': True, 'zones': zones})

@app.route('/download-rings', methods=['POST'])
def download_rings():
    data = request.json
    subject_type = data.get('subject_type')
    latitude = float(data.get('latitude'))
    longitude = float(data.get('longitude'))

    params = data.get('search_params', {})
    custom_inner = params.get('custom_inner_radius')
    custom_outer = params.get('custom_outer_radius')

    profile = SUBJECT_PROFILES.get(subject_type, {})
    inner_km = float(custom_inner) if custom_inner else profile.get('avg_distance_km', 2.0)
    outer_km = float(custom_outer) if custom_outer else profile.get('max_distance_km', 8.0)

    gpx_data = build_rings_gpx(latitude, longitude, inner_km, outer_km)

    return Response(
        gpx_data,
        mimetype='application/gpx+xml',
        headers={'Content-Disposition': 'attachment;filename=MARLY_range_rings.gpx'}
    )

@app.route('/download-sectors', methods=['POST'])
def download_sectors():
    data = request.json
    subject_type = data.get('subject_type')
    latitude = float(data.get('latitude'))
    longitude = float(data.get('longitude'))
    notes = data.get('notes', '')

    params = data.get('search_params', {})
    custom_inner = params.get('custom_inner_radius')
    custom_outer = params.get('custom_outer_radius')
    max_sector_sq_km = params.get('max_sector_sq_km')

    zones = calculate_search_zones(
        latitude, longitude, subject_type, notes,
        custom_inner=custom_inner,
        custom_outer=custom_outer,
        max_sector_sq_km=max_sector_sq_km,
    )

    profile = SUBJECT_PROFILES.get(subject_type, {})
    inner_km = float(custom_inner) if custom_inner else profile.get('avg_distance_km', 2.0)
    outer_km = float(custom_outer) if custom_outer else profile.get('max_distance_km', 8.0)

    sector_weights = {}
    for s in zones['inner_sectors']:
        sector_weights[s['name']] = s['weight']

    max_sq = float(max_sector_sq_km) if max_sector_sq_km else None
    gpx_data = build_sectors_gpx(latitude, longitude, inner_km, outer_km, sector_weights, max_sq)

    return Response(
        gpx_data,
        mimetype='application/gpx+xml',
        headers={'Content-Disposition': 'attachment;filename=MARLY_search_sectors.gpx'}
    )

def calculate_search_zones(lat, lon, subject_type, notes='',
                           custom_inner=None, custom_outer=None,
                           max_sector_sq_km=None, num_teams=None,
                           team_capability=None, urgency_hours=None):
    profile = SUBJECT_PROFILES.get(subject_type, {})
    inner_radius_km = float(custom_inner) if custom_inner else profile.get('avg_distance_km', 2.0)
    outer_radius_km = float(custom_outer) if custom_outer else profile.get('max_distance_km', 8.0)

    sectors = ['N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW']

    direction_keywords = {
        'north': 'N', 'northeast': 'NE', 'east': 'E',
        'southeast': 'SE', 'south': 'S', 'southwest': 'SW',
        'west': 'W', 'northwest': 'NW',
    }

    travel_direction = None
    notes_lower = notes.lower()
    for keyword, bearing in direction_keywords.items():
        if keyword in notes_lower:
            travel_direction = bearing
            break

    sector_weights = {}
    for sector in sectors:
        weight = 1.0
        if subject_type == 'dementia' and travel_direction == sector:
            weight *= 1.5
        elif travel_direction == sector:
            weight *= 1.3
        sector_weights[sector] = round(weight, 1)

    # Calculate sector areas
    sector_span = 45  # degrees
    inner_sector_area = sector_area_sq_km(0, inner_radius_km, sector_span)
    outer_sector_area = sector_area_sq_km(inner_radius_km, outer_radius_km, sector_span)

    inner_sectors = []
    sector_num = 1
    for sector in sectors:
        subs = 0
        if max_sector_sq_km and inner_sector_area > float(max_sector_sq_km):
            subs = math.ceil(inner_sector_area / float(max_sector_sq_km))

        if subs > 0:
            for s in range(subs):
                inner_sectors.append({
                    'name': sector,
                    'label': f'Sector-{sector_num:02d}',
                    'priority': 1,
                    'weight': sector_weights[sector],
                    'radius_km': inner_radius_km,
                    'area_sq_km': round(inner_sector_area / subs, 2),
                })
                sector_num += 1
        else:
            inner_sectors.append({
                'name': sector,
                'label': f'Sector-{sector_num:02d}',
                'priority': 1,
                'weight': sector_weights[sector],
                'radius_km': inner_radius_km,
                'area_sq_km': round(inner_sector_area, 2),
            })
            sector_num += 1

    outer_sectors = []
    outer_num = 1
    for sector in sectors:
        subs = 0
        if max_sector_sq_km and outer_sector_area > float(max_sector_sq_km):
            subs = math.ceil(outer_sector_area / float(max_sector_sq_km))

        if subs > 0:
            for s in range(subs):
                outer_sectors.append({
                    'name': sector,
                    'label': f'Sector-{outer_num:02d}A',
                    'priority': 2,
                    'weight': sector_weights[sector],
                    'inner_radius_km': inner_radius_km,
                    'outer_radius_km': outer_radius_km,
                    'area_sq_km': round(outer_sector_area / subs, 2),
                })
                outer_num += 1
        else:
            outer_sectors.append({
                'name': sector,
                'label': f'Sector-{outer_num:02d}A',
                'priority': 2,
                'weight': sector_weights[sector],
                'inner_radius_km': inner_radius_km,
                'outer_radius_km': outer_radius_km,
                'area_sq_km': round(outer_sector_area, 2),
            })
            outer_num += 1

    return {
        'lat': lat,
        'lon': lon,
        'inner_radius_km': inner_radius_km,
        'outer_radius_km': outer_radius_km,
        'travel_direction': travel_direction,
        'inner_sectors': inner_sectors,
        'outer_sectors': outer_sectors,
        'search_params': {
            'max_sector_sq_km': max_sector_sq_km,
            'num_teams': num_teams,
            'team_capability': team_capability,
            'urgency_hours': urgency_hours,
        }
    }

if __name__ == '__main__':
    app.run(debug=True, port=5000)
