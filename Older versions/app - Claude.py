from flask import Flask, render_template, request, jsonify, Response
from datetime import datetime
from werkzeug.utils import secure_filename
import json
import os
import math
import requests
from lxml import etree

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = 50 * 1024 * 1024

uploaded_trail_data = {'nodes': [], 'filename': ''}

# All distances stored in km internally
SUBJECT_PROFILES = {
    'dementia': {'ring_25_km': 0.6, 'ring_50_km': 1.2, 'ring_75_km': 2.4, 'ring_95_km': 8.0},
    'lost_child': {'ring_25_km': 0.4, 'ring_50_km': 0.8, 'ring_75_km': 1.6, 'ring_95_km': 4.5},
    'lost_hiker': {'ring_25_km': 1.5, 'ring_50_km': 3.0, 'ring_75_km': 5.0, 'ring_95_km': 25.0},
    'lost_hunter': {'ring_25_km': 1.0, 'ring_50_km': 2.5, 'ring_75_km': 4.0, 'ring_95_km': 15.0},
    'lost_vehicle': {'ring_25_km': 3.0, 'ring_50_km': 6.0, 'ring_75_km': 10.0, 'ring_95_km': 50.0},
    'mental_health': {'ring_25_km': 0.8, 'ring_50_km': 1.5, 'ring_75_km': 3.0, 'ring_95_km': 8.0},
}

MARKER_TYPES = {
    'icp': {'name': 'Incident Command Post', 'icon': 'http://caltopo.com/icon.png?cfg=cp%231.0'},
    'ipp': {'name': 'Initial Planning Point', 'icon': 'http://caltopo.com/icon.png?cfg=point-last-seen%231.0'},
    'staging': {'name': 'Staging Area', 'icon': 'http://caltopo.com/icon.png?cfg=staging%231.0'},
    'roadblock': {'name': 'Road Block / Access Point', 'icon': 'http://caltopo.com/icon.png?cfg=road-block%231.0'},
    'hazard': {'name': 'Known Hazard', 'icon': 'http://caltopo.com/icon.png?cfg=safety-hazard%231.0'},
    'wx_weather': {'name': 'Wx-Weather', 'icon': 'http://caltopo.com/icon.png?cfg=lookout%231.0'},
    'medical': {'name': 'Medical Station', 'icon': 'http://caltopo.com/icon.png?cfg=first-aid%231.0'},
    'terrain': {'name': 'Terrain', 'icon': 'http://caltopo.com/icon.png?cfg=aerial-ignition%400%231.0'},
}

LKP_ICON = 'http://caltopo.com/icon.png?cfg=heatsource%231.0'
RING_COLORS = {25: 'ff00ff00', 50: 'ff00ffff', 75: 'ff0080ff', 95: 'ff0000ff'}

# Unit conversions
MI_TO_KM = 1.60934
FT_TO_M = 0.3048
ACRES_TO_SQKM = 0.00404686

# --- Geometry helpers ---

def km_to_lat(km):
    return km / 111.32

def km_to_lon(km, lat):
    return km / (111.32 * math.cos(math.radians(lat)))

def m_to_lat(m):
    return m / 111320.0

def m_to_lon(m, lat):
    return m / (111320.0 * math.cos(math.radians(lat)))

def distance_km(lat1, lon1, lat2, lon2):
    dlat = (lat2 - lat1) * 111.32
    dlon = (lon2 - lon1) * 111.32 * math.cos(math.radians((lat1 + lat2) / 2))
    return math.sqrt(dlat * dlat + dlon * dlon)

def bearing_from_center(center_lat, center_lon, point_lat, point_lon):
    dlat = point_lat - center_lat
    dlon = (point_lon - center_lon) * math.cos(math.radians(center_lat))
    angle = math.degrees(math.atan2(dlon, dlat))
    if angle < 0:
        angle += 360
    directions = ['N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW']
    return directions[round(angle / 45) % 8]

def circle_points(center_lat, center_lon, radius_km, num_points=72):
    points = []
    for i in range(num_points + 1):
        angle = math.radians(i * 360 / num_points)
        dlat = km_to_lat(radius_km * math.cos(angle))
        dlon = km_to_lon(radius_km * math.sin(angle), center_lat)
        points.append((center_lat + dlat, center_lon + dlon))
    return points

def sector_points(center_lat, center_lon, inner_km, outer_km, start_angle, end_angle, num_arc_points=12):
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
    angle_radians = math.radians(angle_degrees)
    return 0.5 * outer_km * outer_km * angle_radians - 0.5 * inner_km * inner_km * angle_radians

def default_marker_position(center_lat, center_lon, ring_km, marker_index):
    offset_km = ring_km * 1.15
    base_lat = center_lat + km_to_lat(0.3 * marker_index)
    base_lon = center_lon - km_to_lon(offset_km, center_lat)
    return base_lat, base_lon

def build_corridor_polygon(trail_points, offset_meters):
    if len(trail_points) < 2:
        return []
    left_side = []
    right_side = []
    for i in range(len(trail_points)):
        lat1, lon1 = trail_points[i]
        if i < len(trail_points) - 1:
            lat2, lon2 = trail_points[i + 1]
        else:
            lat1_prev, lon1_prev = trail_points[i - 1]
            lat2, lon2 = lat1 + (lat1 - lat1_prev), lon1 + (lon1 - lon1_prev)
        dlat = lat2 - lat1
        dlon = (lon2 - lon1) * math.cos(math.radians(lat1))
        if dlat == 0 and dlon == 0:
            if i > 0:
                dlat = lat1 - trail_points[i-1][0]
                dlon = (lon1 - trail_points[i-1][1]) * math.cos(math.radians(lat1))
            if dlat == 0 and dlon == 0:
                continue
        length = math.sqrt(dlat * dlat + dlon * dlon)
        perp_lat = -dlon / length
        perp_lon = dlat / length
        offset_lat = m_to_lat(offset_meters) * perp_lat
        offset_lon = m_to_lon(offset_meters, lat1) * perp_lon
        left_side.append((lat1 + offset_lat, lon1 + offset_lon))
        right_side.append((lat1 - offset_lat, lon1 - offset_lon))
    polygon = left_side + list(reversed(right_side))
    if polygon:
        polygon.append(polygon[0])
    return polygon

def merge_connected_ways(ways, min_dead_end_m=50):
    if not ways:
        return []
    endpoint_to_ways = {}
    for i, way in enumerate(ways):
        if len(way['points']) < 2:
            continue
        start = way['points'][0]
        end = way['points'][-1]
        start_key = (round(start[0], 5), round(start[1], 5))
        end_key = (round(end[0], 5), round(end[1], 5))
        endpoint_to_ways.setdefault(start_key, []).append(('start', i))
        endpoint_to_ways.setdefault(end_key, []).append(('end', i))
    merged = [False] * len(ways)
    result = []
    for i, way in enumerate(ways):
        if merged[i] or len(way['points']) < 2:
            continue
        chain_points = list(way['points'])
        chain_type = way['type']
        chain_name = way['name']
        merged[i] = True
        changed = True
        while changed:
            changed = False
            end_pt = chain_points[-1]
            end_key = (round(end_pt[0], 5), round(end_pt[1], 5))
            if end_key in endpoint_to_ways:
                for pos, j in endpoint_to_ways[end_key]:
                    if not merged[j] and ways[j]['type'] == chain_type:
                        merged[j] = True
                        if pos == 'start':
                            chain_points.extend(ways[j]['points'][1:])
                        else:
                            chain_points.extend(reversed(ways[j]['points'][:-1]))
                        changed = True
                        break
        changed = True
        while changed:
            changed = False
            start_pt = chain_points[0]
            start_key = (round(start_pt[0], 5), round(start_pt[1], 5))
            if start_key in endpoint_to_ways:
                for pos, j in endpoint_to_ways[start_key]:
                    if not merged[j] and ways[j]['type'] == chain_type:
                        merged[j] = True
                        if pos == 'end':
                            new_points = list(ways[j]['points'][:-1])
                            new_points.extend(chain_points)
                            chain_points = new_points
                        else:
                            new_points = list(reversed(ways[j]['points'][1:]))
                            new_points.extend(chain_points)
                            chain_points = new_points
                        changed = True
                        break
        total_length = sum(distance_km(chain_points[k][0], chain_points[k][1], chain_points[k+1][0], chain_points[k+1][1]) for k in range(len(chain_points)-1))
        total_length_m = total_length * 1000
        start_key = (round(chain_points[0][0], 5), round(chain_points[0][1], 5))
        end_key = (round(chain_points[-1][0], 5), round(chain_points[-1][1], 5))
        is_dead_end = len(endpoint_to_ways.get(start_key, [])) <= 1 or len(endpoint_to_ways.get(end_key, [])) <= 1
        if is_dead_end and total_length_m < min_dead_end_m:
            continue
        result.append({'name': chain_name, 'type': chain_type, 'points': chain_points, 'length_km': total_length})
    print(f"Merged {len(ways)} segments into {len(result)} corridors")
    return result

# --- File parsers ---

def parse_kml_trails(file_content):
    trail_nodes = []
    try:
        root = etree.fromstring(file_content)
        for coords_el in root.iter('{http://www.opengis.net/kml/2.2}coordinates'):
            coords_text = coords_el.text
            if not coords_text:
                continue
            parent = coords_el.getparent()
            parent_tag = parent.tag.split('}')[-1] if '}' in parent.tag else parent.tag
            if parent_tag == 'LinearRing':
                gp = parent.getparent()
                gp_tag = gp.tag.split('}')[-1] if '}' in gp.tag else gp.tag
                if gp_tag in ['outerBoundaryIs', 'innerBoundaryIs']:
                    continue
            for coord in coords_text.strip().split():
                parts = coord.split(',')
                if len(parts) >= 2:
                    try:
                        trail_nodes.append({'lat': float(parts[1]), 'lon': float(parts[0]), 'type': 'trail', 'weight': 2.0})
                    except ValueError:
                        continue
        print(f"Parsed {len(trail_nodes)} nodes from KML")
    except Exception as e:
        print(f"KML parse error: {e}")
    return trail_nodes

def parse_gpx_trails(file_content):
    trail_nodes = []
    try:
        root = etree.fromstring(file_content)
        for trkpt in root.iter('{http://www.topografix.com/GPX/1/1}trkpt'):
            try:
                trail_nodes.append({'lat': float(trkpt.get('lat')), 'lon': float(trkpt.get('lon')), 'type': 'trail', 'weight': 2.0})
            except (ValueError, TypeError):
                continue
        for rtept in root.iter('{http://www.topografix.com/GPX/1/1}rtept'):
            try:
                trail_nodes.append({'lat': float(rtept.get('lat')), 'lon': float(rtept.get('lon')), 'type': 'trail', 'weight': 2.0})
            except (ValueError, TypeError):
                continue
        print(f"Parsed {len(trail_nodes)} nodes from GPX")
    except Exception as e:
        print(f"GPX parse error: {e}")
    return trail_nodes

def filter_trail_nodes_by_radius(trail_nodes, center_lat, center_lon, radius_km):
    return [n for n in trail_nodes if distance_km(center_lat, center_lon, n['lat'], n['lon']) <= radius_km]

# --- Terrain data ---

def fetch_trail_data(lat, lon, radius_km):
    radius_meters = int(radius_km * 1000)
    query = '[out:json][timeout:30];(way["highway"~"path|track|footway|bridleway|cycleway"](around:' + str(radius_meters) + ',' + str(lat) + ',' + str(lon) + ');way["highway"~"residential|tertiary|secondary|primary|unclassified|service"](around:' + str(radius_meters) + ',' + str(lat) + ',' + str(lon) + '););out body;>;out skel qt;'
    try:
        print(f"Fetching terrain data for {lat},{lon} radius {radius_km}km...")
        servers = ['https://overpass-api.de/api/interpreter', 'https://overpass.kumi.systems/api/interpreter']
        response = None
        for server in servers:
            try:
                response = requests.post(server, data={'data': query}, headers={'Accept': 'application/json', 'User-Agent': 'MARLY/1.0'}, timeout=30)
                if response.status_code == 200:
                    break
            except:
                continue
        if response is None or response.status_code != 200:
            return [], []
        data = response.json()
        nodes = {}
        trail_nodes = []
        ways = []
        for el in data.get('elements', []):
            if el['type'] == 'node':
                nodes[el['id']] = (el['lat'], el['lon'])
        for el in data.get('elements', []):
            if el['type'] == 'way':
                ht = el.get('tags', {}).get('highway', '')
                is_trail = ht in ['path', 'track', 'footway', 'bridleway', 'cycleway']
                way_name = el.get('tags', {}).get('name', f'Trail-{el["id"]}')
                way_points = []
                for nid in el.get('nodes', []):
                    if nid in nodes:
                        nl, no = nodes[nid]
                        trail_nodes.append({'lat': nl, 'lon': no, 'type': 'trail' if is_trail else 'road', 'weight': 2.0 if is_trail else 1.0})
                        way_points.append((nl, no))
                if way_points:
                    ways.append({'name': way_name, 'type': 'trail' if is_trail else 'road', 'points': way_points})
        print(f"Found {len(trail_nodes)} nodes, {len(ways)} ways")
        return trail_nodes, ways
    except Exception as e:
        print(f"Overpass API error: {e}")
        return [], []

def calculate_terrain_weights_grid(trail_nodes, center_lat, center_lon, outer_km, grid_cell_km):
    lat_offset = km_to_lat(outer_km)
    lon_offset = km_to_lon(outer_km, center_lat)
    cell_lat = km_to_lat(grid_cell_km)
    cell_lon = km_to_lon(grid_cell_km, center_lat)
    cell_counts = {}
    for node in trail_nodes:
        row = int((node['lat'] - (center_lat - lat_offset)) / cell_lat)
        col = int((node['lon'] - (center_lon - lon_offset)) / cell_lon)
        cell_counts[(row, col)] = cell_counts.get((row, col), 0) + node['weight']
    return cell_counts

def apply_terrain_multiplier(base_weight, trail_count, max_count):
    if max_count == 0:
        return base_weight
    return round(base_weight * (1.0 + 0.5 * trail_count / max_count), 2)

# --- KML helpers ---

def coords_to_kml_string(points):
    return ' '.join(f'{lon:.6f},{lat:.6f},0' for lat, lon in points)

def add_kml_polygon(parent, name, desc, points, weight=1.0):
    pm = etree.SubElement(parent, 'Placemark')
    etree.SubElement(pm, 'name').text = name
    etree.SubElement(pm, 'description').text = desc
    ss = etree.SubElement(pm, 'Style')
    sl = etree.SubElement(ss, 'LineStyle')
    etree.SubElement(sl, 'color').text = 'FF0000ff' if weight > 1.0 else 'FF333333'
    etree.SubElement(sl, 'width').text = '2.0'
    sp = etree.SubElement(ss, 'PolyStyle')
    etree.SubElement(sp, 'color').text = '660000ff' if weight > 1.0 else '00000000'
    poly = etree.SubElement(pm, 'Polygon')
    etree.SubElement(poly, 'tessellate').text = '1'
    ob = etree.SubElement(poly, 'outerBoundaryIs')
    lr = etree.SubElement(ob, 'LinearRing')
    etree.SubElement(lr, 'coordinates').text = coords_to_kml_string(points)

def build_combined_kml(lat, lon, selected_rings, sector_data_all, markers=None, sector_shape='grid', grid_cell_km=None, max_sector_sq_km=None):
    kml = etree.Element('kml', xmlns='http://www.opengis.net/kml/2.2')
    doc = etree.SubElement(kml, 'Document')
    etree.SubElement(doc, 'name').text = 'MARLY Search Plan'

    # LKP
    lkp_pm = etree.SubElement(doc, 'Placemark')
    ls = etree.SubElement(lkp_pm, 'Style')
    li = etree.SubElement(ls, 'IconStyle')
    etree.SubElement(li, 'hotSpot', x='0.5', xunits='fraction', y='0.5', yunits='fraction')
    lic = etree.SubElement(li, 'Icon')
    etree.SubElement(lic, 'href').text = LKP_ICON
    etree.SubElement(lkp_pm, 'name').text = 'Last Known Position'
    pt = etree.SubElement(lkp_pm, 'Point')
    etree.SubElement(pt, 'coordinates').text = f'{lon:.6f},{lat:.6f},0'

    # Markers
    if markers:
        mf = etree.SubElement(doc, 'Folder')
        etree.SubElement(mf, 'open').text = '1'
        etree.SubElement(mf, 'name').text = 'Operational Markers'
        for m in markers:
            pm = etree.SubElement(mf, 'Placemark')
            ms = etree.SubElement(pm, 'Style')
            mi = etree.SubElement(ms, 'IconStyle')
            etree.SubElement(mi, 'hotSpot', x='0.5', xunits='fraction', y='0.5', yunits='fraction')
            mic = etree.SubElement(mi, 'Icon')
            etree.SubElement(mic, 'href').text = MARKER_TYPES.get(m['type'], {}).get('icon', '')
            etree.SubElement(pm, 'name').text = m['name']
            if m.get('notes'):
                etree.SubElement(pm, 'description').text = m['notes']
            p = etree.SubElement(pm, 'Point')
            etree.SubElement(p, 'coordinates').text = f'{m["lon"]:.6f},{m["lat"]:.6f},0'

    # Rings
    rf = etree.SubElement(doc, 'Folder')
    etree.SubElement(rf, 'open').text = '1'
    etree.SubElement(rf, 'name').text = 'Probability Rings'
    for ring in selected_rings:
        pm = etree.SubElement(rf, 'Placemark')
        rs = etree.SubElement(pm, 'Style')
        rl = etree.SubElement(rs, 'LineStyle')
        etree.SubElement(rl, 'color').text = RING_COLORS.get(ring['pct'], 'ffffffff')
        etree.SubElement(rl, 'width').text = '3.0'
        etree.SubElement(pm, 'name').text = f'{ring["pct"]}% Ring ({ring["km"]:.2f} km / {ring["km"]/MI_TO_KM:.2f} mi)'
        lss = etree.SubElement(pm, 'LineString')
        etree.SubElement(lss, 'altitudeMode').text = 'clampToGround'
        etree.SubElement(lss, 'tessellate').text = '1'
        etree.SubElement(lss, 'coordinates').text = coords_to_kml_string(circle_points(lat, lon, ring['km']))

    # Sectors
    for ring_data in sector_data_all:
        folder = etree.SubElement(doc, 'Folder')
        etree.SubElement(folder, 'name').text = ring_data['ring_label']
        inner_km = ring_data['inner_km']
        outer_km = ring_data['outer_km']

        if sector_shape == 'grid':
            cell_km = float(grid_cell_km) if grid_cell_km else 0.35
            full_outer = selected_rings[-1]['km']
            lo = km_to_lat(full_outer)
            lo2 = km_to_lon(full_outer, lat)
            cld = km_to_lat(cell_km)
            cod = km_to_lon(cell_km, lat)
            for s in ring_data['sectors']:
                row, col = s.get('grid_row', 0), s.get('grid_col', 0)
                ml = (lat - lo) + row * cld
                mo = (lon - lo2) + col * cod
                corners = [(ml, mo), (ml+cld, mo), (ml+cld, mo+cod), (ml, mo+cod), (ml, mo)]
                add_kml_polygon(folder, f'{s["label"]} ({s["direction"]} Wt:{s["weight"]})', f'{ring_data["ring_label"]} - Weight {s["weight"]}', corners, s['weight'])
        else:
            sn = ['N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW']
            ba = [0, 45, 90, 135, 180, 225, 270, 315]
            wl = {}
            for s in ring_data['sectors']:
                if s['direction'] not in wl:
                    wl[s['direction']] = s['weight']
            for name, base_angle in zip(sn, ba):
                area = sector_area_sq_km(inner_km, outer_km, 45)
                if max_sector_sq_km and area > float(max_sector_sq_km):
                    subdivisions = math.ceil(area / float(max_sector_sq_km))
                    sub_span = 45 / subdivisions
                    matching = [s for s in ring_data['sectors'] if s['direction'] == name]
                    for si, sector in enumerate(matching):
                        sa = (base_angle - 22.5) + si * sub_span
                        ea = sa + sub_span
                        pts = sector_points(lat, lon, inner_km, outer_km, sa, ea)
                        add_kml_polygon(folder, f'{sector["label"]} ({name} Wt:{sector["weight"]})', f'{ring_data["ring_label"]}', pts, sector['weight'])
                else:
                    sector = next((s for s in ring_data['sectors'] if s['direction'] == name), None)
                    if sector:
                        pts = sector_points(lat, lon, inner_km, outer_km, base_angle - 22.5, base_angle + 22.5)
                        add_kml_polygon(folder, f'{sector["label"]} ({name} Wt:{sector["weight"]})', f'{ring_data["ring_label"]}', pts, sector['weight'])

    return etree.tostring(kml, pretty_print=True, xml_declaration=True, encoding='UTF-8')

# --- Hasty KML ---

def build_hasty_kml(lat, lon, ring_km, corridors, grid_sectors=None):
    kml = etree.Element('kml', xmlns='http://www.opengis.net/kml/2.2')
    doc = etree.SubElement(kml, 'Document')
    etree.SubElement(doc, 'name').text = 'MARLY Hasty Search Plan'

    # LKP
    lkp_pm = etree.SubElement(doc, 'Placemark')
    ls = etree.SubElement(lkp_pm, 'Style')
    li = etree.SubElement(ls, 'IconStyle')
    etree.SubElement(li, 'hotSpot', x='0.5', xunits='fraction', y='0.5', yunits='fraction')
    lic = etree.SubElement(li, 'Icon')
    etree.SubElement(lic, 'href').text = LKP_ICON
    etree.SubElement(lkp_pm, 'name').text = 'Last Known Position'
    pt = etree.SubElement(lkp_pm, 'Point')
    etree.SubElement(pt, 'coordinates').text = f'{lon:.6f},{lat:.6f},0'

    # Ring
    rp = etree.SubElement(doc, 'Placemark')
    rs = etree.SubElement(rp, 'Style')
    rl = etree.SubElement(rs, 'LineStyle')
    etree.SubElement(rl, 'color').text = 'ff00ffff'
    etree.SubElement(rl, 'width').text = '2.0'
    etree.SubElement(rp, 'name').text = f'Hasty Ring ({ring_km:.2f} km / {ring_km/MI_TO_KM:.2f} mi)'
    rls = etree.SubElement(rp, 'LineString')
    etree.SubElement(rls, 'altitudeMode').text = 'clampToGround'
    etree.SubElement(rls, 'tessellate').text = '1'
    etree.SubElement(rls, 'coordinates').text = coords_to_kml_string(circle_points(lat, lon, ring_km))

    # Corridors
    cf = etree.SubElement(doc, 'Folder')
    etree.SubElement(cf, 'open').text = '1'
    etree.SubElement(cf, 'name').text = 'Trail Corridors'
    for c in corridors:
        pm = etree.SubElement(cf, 'Placemark')
        etree.SubElement(pm, 'name').text = c['label']
        etree.SubElement(pm, 'description').text = f'{c["trail_name"]} - {c["direction"]}'
        cs = etree.SubElement(pm, 'Style')
        cl = etree.SubElement(cs, 'LineStyle')
        etree.SubElement(cl, 'color').text = 'FF00AAFF'
        etree.SubElement(cl, 'width').text = '2.0'
        cp = etree.SubElement(cs, 'PolyStyle')
        etree.SubElement(cp, 'color').text = '5500AAFF'
        poly = etree.SubElement(pm, 'Polygon')
        etree.SubElement(poly, 'tessellate').text = '1'
        ob = etree.SubElement(poly, 'outerBoundaryIs')
        lr = etree.SubElement(ob, 'LinearRing')
        etree.SubElement(lr, 'coordinates').text = coords_to_kml_string(c['polygon'])

    # Grid sectors for gaps
    if grid_sectors:
        sf = etree.SubElement(doc, 'Folder')
        etree.SubElement(sf, 'open').text = '1'
        etree.SubElement(sf, 'name').text = 'Hasty Search Sectors'
        for s in grid_sectors:
            add_kml_polygon(sf, s['label'], f'{s["direction"]} - {s["area_acres"]:.0f} acres', s['corners'], 1.0)

    return etree.tostring(kml, pretty_print=True, xml_declaration=True, encoding='UTF-8')

# --- Routes ---

@app.route('/')
def index():
    return render_template('form.html')

@app.route('/hasty')
def hasty():
    return render_template('hasty.html')

@app.route('/submit', methods=['POST'])
def submit_form():
    data = request.json
    with open('search_plans.json', 'a') as f:
        f.write(json.dumps({'timestamp': datetime.now().isoformat(), **{k: data.get(k) for k in ['subject_type','latitude','longitude','time_last_seen','age','terrain','notes']}}) + '\n')
    return jsonify({'success': True})

@app.route('/upload-trail-file', methods=['POST'])
def upload_trail_file():
    global uploaded_trail_data
    if 'trail_file' not in request.files:
        return jsonify({'success': False, 'error': 'No file'})
    file = request.files['trail_file']
    if file.filename == '':
        return jsonify({'success': False, 'error': 'No file selected'})
    filename = secure_filename(file.filename)
    content = file.read()
    ext = filename.lower().split('.')[-1]
    if ext == 'kml':
        nodes = parse_kml_trails(content)
    elif ext == 'gpx':
        nodes = parse_gpx_trails(content)
    else:
        return jsonify({'success': False, 'error': 'Use .kml or .gpx'})
    uploaded_trail_data = {'nodes': nodes, 'filename': filename}
    return jsonify({'success': True, 'filename': filename, 'total_nodes': len(nodes)})

@app.route('/generate-search-plan', methods=['POST'])
def generate_search_plan():
    data = request.json
    zones = calculate_search_zones(float(data['latitude']), float(data['longitude']), data.get('subject_type'), data.get('notes', ''), data.get('search_params', {}))
    return jsonify({'success': True, 'zones': zones})

@app.route('/generate-hasty', methods=['POST'])
def generate_hasty():
    data = request.json
    lat, lon = float(data['latitude']), float(data['longitude'])
    subject_type = data.get('subject_type')
    offset_m = float(data.get('offset_meters', 30))
    ring_pct = data.get('ring_pct', '50')
    sector_size_acres = float(data.get('sector_size_acres', 30))

    profile = SUBJECT_PROFILES.get(subject_type, {})
    ring_km = profile.get(f'ring_{ring_pct}_km', 2.0)
    custom_km = data.get('custom_ring_km')
    if custom_km:
        ring_km = float(custom_km)

    trail_nodes, ways = fetch_trail_data(lat, lon, ring_km)
    merged_ways = merge_connected_ways(ways, min_dead_end_m=50)

    # Build corridors
    final_ways = []
    for way in merged_ways:
        fp = [(p[0], p[1]) for p in way['points'] if distance_km(lat, lon, p[0], p[1]) <= ring_km]
        if len(fp) >= 2:
            avg_dist = sum(distance_km(lat, lon, p[0], p[1]) for p in fp) / len(fp)
            direction = bearing_from_center(lat, lon, fp[len(fp)//2][0], fp[len(fp)//2][1])
            length = sum(distance_km(fp[i][0], fp[i][1], fp[i+1][0], fp[i+1][1]) for i in range(len(fp)-1))
            final_ways.append({'name': way['name'], 'type': way['type'], 'points': fp, 'avg_dist': avg_dist, 'direction': direction, 'length_km': length})
    final_ways.sort(key=lambda w: (0 if w['type'] == 'trail' else 1, w['avg_dist']))

    corridors = []
    corridor_trail_nodes = set()
    for i, way in enumerate(final_ways):
        polygon = build_corridor_polygon(way['points'], offset_m)
        if polygon:
            corridors.append({'label': f'Hasty-{i+1:02d}', 'trail_name': way['name'], 'direction': way['direction'], 'type': way['type'], 'length_km': way['length_km'], 'avg_dist_km': round(way['avg_dist'], 2), 'polygon': polygon})
            for p in way['points']:
                corridor_trail_nodes.add((round(p[0], 5), round(p[1], 5)))

    # Build grid sectors for gaps
    sector_size_sqkm = sector_size_acres * ACRES_TO_SQKM
    cell_km = math.sqrt(sector_size_sqkm)
    lat_offset = km_to_lat(ring_km)
    lon_offset = km_to_lon(ring_km, lat)
    cell_lat = km_to_lat(cell_km)
    cell_lon = km_to_lon(cell_km, lat)

    grid_sectors = []
    sector_num = 1
    curr_lat = lat - lat_offset
    while curr_lat < lat + lat_offset:
        curr_lon = lon - lon_offset
        while curr_lon < lon + lon_offset:
            cl = curr_lat + cell_lat / 2
            co = curr_lon + cell_lon / 2
            dist = distance_km(lat, lon, cl, co)
            if dist <= ring_km:
                # Check if this cell overlaps with a corridor
                cell_has_trail = False
                for tn in corridor_trail_nodes:
                    if curr_lat <= tn[0] <= curr_lat + cell_lat and curr_lon <= tn[1] <= curr_lon + cell_lon:
                        cell_has_trail = True
                        break
                if not cell_has_trail:
                    direction = bearing_from_center(lat, lon, cl, co)
                    corners = [(curr_lat, curr_lon), (curr_lat+cell_lat, curr_lon), (curr_lat+cell_lat, curr_lon+cell_lon), (curr_lat, curr_lon+cell_lon), (curr_lat, curr_lon)]
                    grid_sectors.append({'label': f'HS-{sector_num:02d}', 'direction': direction, 'area_acres': sector_size_acres, 'area_sq_km': round(sector_size_sqkm, 3), 'dist_km': round(dist, 2), 'corners': corners})
                    sector_num += 1
            curr_lon += cell_lon
        curr_lat += cell_lat

    grid_sectors.sort(key=lambda s: s['dist_km'])
    for i, s in enumerate(grid_sectors):
        s['label'] = f'HS-{i+1:02d}'

    return jsonify({
        'success': True,
        'ring_km': ring_km,
        'ring_mi': round(ring_km / MI_TO_KM, 2),
        'total_ways': len(ways),
        'merged_ways': len(merged_ways),
        'corridors': len(corridors),
        'grid_sectors': len(grid_sectors),
        'sector_size_acres': sector_size_acres,
        'corridor_list': [{'label': c['label'], 'trail_name': c['trail_name'], 'direction': c['direction'], 'type': c['type'], 'length_km': round(c['length_km'], 2), 'length_mi': round(c['length_km']/MI_TO_KM, 2), 'avg_dist_km': c['avg_dist_km']} for c in corridors],
        'sector_list': [{'label': s['label'], 'direction': s['direction'], 'area_acres': s['area_acres'], 'dist_km': s['dist_km']} for s in grid_sectors],
    })

@app.route('/download-hasty', methods=['POST'])
def download_hasty():
    data = request.json
    lat, lon = float(data['latitude']), float(data['longitude'])
    subject_type = data.get('subject_type')
    offset_m = float(data.get('offset_meters', 30))
    ring_pct = data.get('ring_pct', '50')
    sector_size_acres = float(data.get('sector_size_acres', 30))

    profile = SUBJECT_PROFILES.get(subject_type, {})
    ring_km = profile.get(f'ring_{ring_pct}_km', 2.0)
    custom_km = data.get('custom_ring_km')
    if custom_km:
        ring_km = float(custom_km)

    trail_nodes, ways = fetch_trail_data(lat, lon, ring_km)
    merged_ways = merge_connected_ways(ways, min_dead_end_m=50)

    final_ways = []
    for way in merged_ways:
        fp = [(p[0], p[1]) for p in way['points'] if distance_km(lat, lon, p[0], p[1]) <= ring_km]
        if len(fp) >= 2:
            avg_dist = sum(distance_km(lat, lon, p[0], p[1]) for p in fp) / len(fp)
            direction = bearing_from_center(lat, lon, fp[len(fp)//2][0], fp[len(fp)//2][1])
            length = sum(distance_km(fp[i][0], fp[i][1], fp[i+1][0], fp[i+1][1]) for i in range(len(fp)-1))
            final_ways.append({'name': way['name'], 'type': way['type'], 'points': fp, 'avg_dist': avg_dist, 'direction': direction, 'length_km': length})
    final_ways.sort(key=lambda w: (0 if w['type'] == 'trail' else 1, w['avg_dist']))

    corridors = []
    corridor_trail_nodes = set()
    for i, way in enumerate(final_ways):
        polygon = build_corridor_polygon(way['points'], offset_m)
        if polygon:
            corridors.append({'label': f'Hasty-{i+1:02d}', 'trail_name': way['name'], 'direction': way['direction'], 'length_km': way['length_km'], 'polygon': polygon})
            for p in way['points']:
                corridor_trail_nodes.add((round(p[0], 5), round(p[1], 5)))

    sector_size_sqkm = sector_size_acres * ACRES_TO_SQKM
    cell_km = math.sqrt(sector_size_sqkm)
    lat_offset = km_to_lat(ring_km)
    lon_offset = km_to_lon(ring_km, lat)
    cell_lat = km_to_lat(cell_km)
    cell_lon = km_to_lon(cell_km, lat)

    grid_sectors = []
    sector_num = 1
    curr_lat = lat - lat_offset
    while curr_lat < lat + lat_offset:
        curr_lon = lon - lon_offset
        while curr_lon < lon + lon_offset:
            cl = curr_lat + cell_lat / 2
            co = curr_lon + cell_lon / 2
            dist = distance_km(lat, lon, cl, co)
            if dist <= ring_km:
                cell_has_trail = False
                for tn in corridor_trail_nodes:
                    if curr_lat <= tn[0] <= curr_lat + cell_lat and curr_lon <= tn[1] <= curr_lon + cell_lon:
                        cell_has_trail = True
                        break
                if not cell_has_trail:
                    direction = bearing_from_center(lat, lon, cl, co)
                    corners = [(curr_lat, curr_lon), (curr_lat+cell_lat, curr_lon), (curr_lat+cell_lat, curr_lon+cell_lon), (curr_lat, curr_lon+cell_lon), (curr_lat, curr_lon)]
                    grid_sectors.append({'label': f'HS-{sector_num:02d}', 'direction': direction, 'area_acres': sector_size_acres, 'corners': corners})
                    sector_num += 1
            curr_lon += cell_lon
        curr_lat += cell_lat

    grid_sectors.sort(key=lambda s: distance_km(lat, lon, s['corners'][0][0] + cell_lat/2, s['corners'][0][1] + cell_lon/2))
    for i, s in enumerate(grid_sectors):
        s['label'] = f'HS-{i+1:02d}'

    kml_data = build_hasty_kml(lat, lon, ring_km, corridors, grid_sectors)
    return Response(kml_data, mimetype='application/vnd.google-earth.kml+xml', headers={'Content-Disposition': 'attachment;filename=MARLY_hasty_search.kml'})

@app.route('/download-combined', methods=['POST'])
def download_combined():
    data = request.json
    lat, lon = float(data['latitude']), float(data['longitude'])
    params = data.get('search_params', {})
    zones = calculate_search_zones(lat, lon, data.get('subject_type'), data.get('notes', ''), params)

    markers_input = data.get('markers', [])
    third_ring_km = zones['selected_rings'][2]['km'] if len(zones['selected_rings']) > 2 else zones['selected_rings'][-1]['km']
    processed_markers = []
    di = 0
    for m in markers_input:
        mi = MARKER_TYPES.get(m['type'], {})
        mlat, mlon = m.get('lat'), m.get('lon')
        if mlat and mlon:
            mlat, mlon = float(mlat), float(mlon)
        else:
            mlat, mlon = default_marker_position(lat, lon, third_ring_km, di)
            di += 1
        processed_markers.append({'lat': mlat, 'lon': mlon, 'name': mi.get('name', m['type']), 'type': m['type'], 'notes': m.get('notes', '')})

    kml_data = build_combined_kml(lat, lon, zones['selected_rings'], zones['sector_data_all'], markers=processed_markers, sector_shape=params.get('sector_shape', 'grid'), grid_cell_km=params.get('grid_cell_km'), max_sector_sq_km=params.get('max_sector_sq_km'))
    return Response(kml_data, mimetype='application/vnd.google-earth.kml+xml', headers={'Content-Disposition': 'attachment;filename=MARLY_search_plan.kml'})

# --- Core calculation ---

def calculate_search_zones(lat, lon, subject_type, notes, params):
    global uploaded_trail_data
    profile = SUBJECT_PROFILES.get(subject_type, {})
    ring_options = [{'key': 'ring_25', 'pct': 25, 'default_km': profile.get('ring_25_km', 1.0)}, {'key': 'ring_50', 'pct': 50, 'default_km': profile.get('ring_50_km', 2.0)}, {'key': 'ring_75', 'pct': 75, 'default_km': profile.get('ring_75_km', 4.0)}, {'key': 'ring_95', 'pct': 95, 'default_km': profile.get('ring_95_km', 8.0)}]
    selected_rings = []
    for ring in ring_options:
        if params.get(ring['key'], False):
            custom_km = params.get(ring['key'] + '_km')
            km = float(custom_km) if custom_km else ring['default_km']
            selected_rings.append({'pct': ring['pct'], 'km': km})
    if not selected_rings:
        selected_rings = [{'pct': 50, 'km': profile.get('ring_50_km', 2.0)}, {'pct': 95, 'km': profile.get('ring_95_km', 8.0)}]
    selected_rings.sort(key=lambda r: r['km'])

    sectors_list = ['N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW']
    direction_keywords = {'north': 'N', 'northeast': 'NE', 'east': 'E', 'southeast': 'SE', 'south': 'S', 'southwest': 'SW', 'west': 'W', 'northwest': 'NW'}
    travel_direction = None
    notes_lower = notes.lower()
    for kw, b in direction_keywords.items():
        if kw in notes_lower:
            travel_direction = b
            break

    sector_weights = {}
    for sector in sectors_list:
        w = 1.0
        if subject_type == 'dementia' and travel_direction == sector:
            w *= 1.5
        elif travel_direction == sector:
            w *= 1.3
        sector_weights[sector] = round(w, 1)

    terrain_aware = params.get('terrain_aware', False)
    terrain_source = params.get('terrain_source', 'osm')
    trail_nodes = []
    terrain_stats = {}
    if terrain_aware:
        outer_km = selected_rings[-1]['km']
        if terrain_source == 'file' and uploaded_trail_data['nodes']:
            trail_nodes = filter_trail_nodes_by_radius(uploaded_trail_data['nodes'], lat, lon, outer_km)
            terrain_stats = {'source': 'file', 'filename': uploaded_trail_data['filename'], 'total_nodes': len(trail_nodes), 'trail_nodes': len(trail_nodes), 'road_nodes': 0}
        else:
            tn, _ = fetch_trail_data(lat, lon, outer_km)
            trail_nodes = tn
            terrain_stats = {'source': 'osm', 'total_nodes': len(trail_nodes), 'trail_nodes': len([n for n in trail_nodes if n['type'] == 'trail']), 'road_nodes': len([n for n in trail_nodes if n['type'] == 'road'])}

    sector_shape = params.get('sector_shape', 'grid')
    grid_cell_km = params.get('grid_cell_km')
    max_sector_sq_km = params.get('max_sector_sq_km')
    radii = [r['km'] for r in selected_rings]
    sector_data_all = []

    for i in range(len(selected_rings)):
        inner_km = radii[i-1] if i > 0 else 0
        outer_km = radii[i]
        pct = selected_rings[i]['pct']
        priority = i + 1
        ring_label = f'P{priority} ({pct}% ring)'

        if sector_shape == 'grid':
            cell_km = float(grid_cell_km) if grid_cell_km else 0.35
            cell_area = cell_km * cell_km
            lo = km_to_lat(selected_rings[-1]['km'])
            lo2 = km_to_lon(selected_rings[-1]['km'], lat)
            cl = km_to_lat(cell_km)
            co = km_to_lon(cell_km, lat)
            gtc = {}
            if terrain_aware and trail_nodes:
                gtc = calculate_terrain_weights_grid(trail_nodes, lat, lon, selected_rings[-1]['km'], cell_km)
            mtc = max(gtc.values()) if gtc else 0
            cells = []
            curr_lat = lat - lo
            row = 0
            while curr_lat < lat + lo:
                curr_lon = lon - lo2
                col_idx = 0
                while curr_lon < lon + lo2:
                    ccl = curr_lat + cl/2
                    cco = curr_lon + co/2
                    dist = distance_km(lat, lon, ccl, cco)
                    if inner_km < dist <= outer_km:
                        d = bearing_from_center(lat, lon, ccl, cco)
                        bw = sector_weights.get(d, 1.0)
                        tc = gtc.get((row, col_idx), 0)
                        w = apply_terrain_multiplier(bw, tc, mtc) if terrain_aware and mtc > 0 else bw
                        cells.append({'direction': d, 'weight': w, 'dist': round(dist, 2), 'area_sq_km': round(cell_area, 2), 'area_acres': round(cell_area / ACRES_TO_SQKM, 1), 'grid_row': row, 'grid_col': col_idx, 'trail_count': int(tc) if terrain_aware else None})
                    curr_lon += co
                    col_idx += 1
                curr_lat += cl
                row += 1
            cells.sort(key=lambda c: c['dist'])
            suffix = '' if i == 0 else chr(64+i)
            for j, cell in enumerate(cells):
                cell['label'] = f'Sector-{j+1:02d}{suffix}'
                cell['priority'] = priority
            sector_data_all.append({'ring_label': ring_label, 'inner_km': inner_km, 'outer_km': outer_km, 'pct': pct, 'priority': priority, 'sectors': cells})
        else:
            sector_span = 45
            area = sector_area_sq_km(inner_km, outer_km, sector_span)
            rtc = {s: 0.0 for s in sectors_list}
            if terrain_aware and trail_nodes:
                for node in trail_nodes:
                    dist = distance_km(lat, lon, node['lat'], node['lon'])
                    if inner_km < dist <= outer_km:
                        rtc[bearing_from_center(lat, lon, node['lat'], node['lon'])] += node['weight']
            mt = max(rtc.values()) if any(rtc.values()) else 0
            pie_sectors = []
            sn = 1
            suffix = '' if i == 0 else chr(64+i)
            for sector in sectors_list:
                bw = sector_weights[sector]
                tc = rtc.get(sector, 0)
                w = apply_terrain_multiplier(bw, tc, mt) if terrain_aware and mt > 0 else bw
                subs = math.ceil(area / float(max_sector_sq_km)) if max_sector_sq_km and area > float(max_sector_sq_km) else 0
                if subs > 0:
                    for s in range(subs):
                        pie_sectors.append({'direction': sector, 'label': f'Sector-{sn:02d}{suffix}', 'priority': priority, 'weight': w, 'area_sq_km': round(area/subs, 2), 'area_acres': round((area/subs)/ACRES_TO_SQKM, 1), 'trail_count': int(tc) if terrain_aware else None})
                        sn += 1
                else:
                    pie_sectors.append({'direction': sector, 'label': f'Sector-{sn:02d}{suffix}', 'priority': priority, 'weight': w, 'area_sq_km': round(area, 2), 'area_acres': round(area/ACRES_TO_SQKM, 1), 'trail_count': int(tc) if terrain_aware else None})
                    sn += 1
            sector_data_all.append({'ring_label': ring_label, 'inner_km': inner_km, 'outer_km': outer_km, 'pct': pct, 'priority': priority, 'sectors': pie_sectors})

    result = {'lat': lat, 'lon': lon, 'selected_rings': selected_rings, 'travel_direction': travel_direction, 'sector_shape': sector_shape, 'terrain_aware': terrain_aware, 'sector_data_all': sector_data_all, 'search_params': params}
    if terrain_aware:
        result['terrain_stats'] = terrain_stats
    return result

if __name__ == '__main__':
    app.run(debug=True, port=5000)
