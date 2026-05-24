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

SUBJECT_PROFILES = {
    'dementia': {'ring_25_km': 0.6, 'ring_50_km': 1.2, 'ring_75_km': 2.4, 'ring_95_km': 8.0},
    'lost_child': {'ring_25_km': 0.4, 'ring_50_km': 0.8, 'ring_75_km': 1.6, 'ring_95_km': 4.5},
    'lost_hiker': {'ring_25_km': 1.5, 'ring_50_km': 3.0, 'ring_75_km': 5.0, 'ring_95_km': 25.0},
    'lost_hunter': {'ring_25_km': 1.0, 'ring_50_km': 2.5, 'ring_75_km': 4.0, 'ring_95_km': 15.0},
    'mental_health': {'ring_25_km': 0.8, 'ring_50_km': 1.5, 'ring_75_km': 3.0, 'ring_95_km': 8.0},
}

# Category-specific sector templates
SECTOR_TEMPLATES = {
    'dementia': {
        'primary_half_width': 30,     # 60 degree cone total
        'alternate_half_width': 0,     # No alternate zone
        'requires_direction': True,
    },
    'lost_hiker': {
        'primary_half_width': 60,     # 120 degree primary cone
        'alternate_half_width': 90,   # 30 degrees alternate on each side
        'requires_direction': True,
    },
    'lost_hunter': {
        'primary_half_width': 60,     # Same as hiker
        'alternate_half_width': 90,
        'requires_direction': True,
    },
    'lost_child': {'primary_half_width': 180, 'alternate_half_width': 0, 'requires_direction': False},
    'mental_health': {'primary_half_width': 180, 'alternate_half_width': 0, 'requires_direction': False},
}

DIRECTION_ANGLES = {'N': 0, 'NE': 45, 'E': 90, 'SE': 135, 'S': 180, 'SW': 225, 'W': 270, 'NW': 315}

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
MI_TO_KM = 1.60934
FT_TO_M = 0.3048
ACRES_TO_SQKM = 0.00404686

# --- Geometry helpers ---

def km_to_lat(km): return km / 111.32
def km_to_lon(km, lat): return km / (111.32 * math.cos(math.radians(lat)))
def m_to_lat(m): return m / 111320.0
def m_to_lon(m, lat): return m / (111320.0 * math.cos(math.radians(lat)))

def distance_km(lat1, lon1, lat2, lon2):
    dlat = (lat2 - lat1) * 111.32
    dlon = (lon2 - lon1) * 111.32 * math.cos(math.radians((lat1 + lat2) / 2))
    return math.sqrt(dlat * dlat + dlon * dlon)

def bearing_from_center(center_lat, center_lon, point_lat, point_lon):
    dlat = point_lat - center_lat
    dlon = (point_lon - center_lon) * math.cos(math.radians(center_lat))
    angle = math.degrees(math.atan2(dlon, dlat))
    if angle < 0: angle += 360
    directions = ['N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW']
    return directions[round(angle / 45) % 8]

def bearing_angle(center_lat, center_lon, point_lat, point_lon):
    """Get raw bearing angle in degrees (0-360) from center to point."""
    dlat = point_lat - center_lat
    dlon = (point_lon - center_lon) * math.cos(math.radians(center_lat))
    angle = math.degrees(math.atan2(dlon, dlat))
    if angle < 0: angle += 360
    return angle

def angle_in_range(angle, center_angle, half_width):
    """Check if an angle falls within ±half_width of center_angle."""
    if half_width >= 180: return True
    diff = abs(angle - center_angle)
    if diff > 180: diff = 360 - diff
    return diff <= half_width

def classify_sector_zone(angle, center_angle, template):
    """Classify a sector as primary, alternate, or outside based on template."""
    primary_hw = template['primary_half_width']
    alternate_hw = template.get('alternate_half_width', 0)

    if angle_in_range(angle, center_angle, primary_hw):
        return 'primary'
    if alternate_hw > 0 and angle_in_range(angle, center_angle, alternate_hw):
        return 'alternate'
    return 'outside'

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
    return center_lat + km_to_lat(0.3 * marker_index), center_lon - km_to_lon(offset_km, center_lat)

def build_corridor_polygon(trail_points, offset_meters):
    if len(trail_points) < 2: return []
    left_side, right_side = [], []
    for i in range(len(trail_points)):
        lat1, lon1 = trail_points[i]
        if i < len(trail_points) - 1:
            lat2, lon2 = trail_points[i + 1]
        else:
            lat1p, lon1p = trail_points[i - 1]
            lat2, lon2 = lat1 + (lat1 - lat1p), lon1 + (lon1 - lon1p)
        dlat = lat2 - lat1
        dlon = (lon2 - lon1) * math.cos(math.radians(lat1))
        if dlat == 0 and dlon == 0:
            if i > 0:
                dlat = lat1 - trail_points[i-1][0]
                dlon = (lon1 - trail_points[i-1][1]) * math.cos(math.radians(lat1))
            if dlat == 0 and dlon == 0: continue
        length = math.sqrt(dlat * dlat + dlon * dlon)
        perp_lat, perp_lon = -dlon / length, dlat / length
        ol, oo = m_to_lat(offset_meters) * perp_lat, m_to_lon(offset_meters, lat1) * perp_lon
        left_side.append((lat1 + ol, lon1 + oo))
        right_side.append((lat1 - ol, lon1 - oo))
    polygon = left_side + list(reversed(right_side))
    if polygon: polygon.append(polygon[0])
    return polygon

def merge_connected_ways(ways, min_dead_end_m=50):
    if not ways: return []
    ep = {}
    for i, way in enumerate(ways):
        if len(way['points']) < 2: continue
        sk = (round(way['points'][0][0], 5), round(way['points'][0][1], 5))
        ek = (round(way['points'][-1][0], 5), round(way['points'][-1][1], 5))
        ep.setdefault(sk, []).append(('start', i))
        ep.setdefault(ek, []).append(('end', i))
    merged = [False] * len(ways)
    result = []
    for i, way in enumerate(ways):
        if merged[i] or len(way['points']) < 2: continue
        chain = list(way['points']); ct = way['type']; cn = way['name']; merged[i] = True
        for direction in ['forward', 'backward']:
            changed = True
            while changed:
                changed = False
                pt = chain[-1] if direction == 'forward' else chain[0]
                key = (round(pt[0], 5), round(pt[1], 5))
                if key in ep:
                    for pos, j in ep[key]:
                        if not merged[j] and ways[j]['type'] == ct:
                            merged[j] = True
                            if direction == 'forward':
                                chain.extend(ways[j]['points'][1:] if pos == 'start' else list(reversed(ways[j]['points'][:-1])))
                            else:
                                new = list(ways[j]['points'][:-1]) if pos == 'end' else list(reversed(ways[j]['points'][1:]))
                                new.extend(chain); chain = new
                            changed = True; break
        tl = sum(distance_km(chain[k][0], chain[k][1], chain[k+1][0], chain[k+1][1]) for k in range(len(chain)-1))
        sk = (round(chain[0][0], 5), round(chain[0][1], 5))
        ek = (round(chain[-1][0], 5), round(chain[-1][1], 5))
        is_de = len(ep.get(sk, [])) <= 1 or len(ep.get(ek, [])) <= 1
        if is_de and tl * 1000 < min_dead_end_m: continue
        result.append({'name': cn, 'type': ct, 'points': chain, 'length_km': tl})
    print(f"Merged {len(ways)} segments into {len(result)} corridors")
    return result

# --- Corridor builder (shared by hasty and full-plan) ---

def build_corridors_from_data(lat, lon, outer_km, ways, offset_m, feature_type='both'):
    """Build trail/road corridor polygons from OSM way data."""
    if not ways:
        return []
    # Filter by feature type
    if feature_type == 'trails':
        ways = [w for w in ways if w['type'] == 'trail']
    elif feature_type == 'roads':
        ways = [w for w in ways if w['type'] == 'road']

    merged_ways = merge_connected_ways(ways, min_dead_end_m=50)

    final_ways = []
    for way in merged_ways:
        fp = [(p[0], p[1]) for p in way['points'] if distance_km(lat, lon, p[0], p[1]) <= outer_km]
        if len(fp) >= 2:
            avg_dist = sum(distance_km(lat, lon, p[0], p[1]) for p in fp) / len(fp)
            direction = bearing_from_center(lat, lon, fp[len(fp)//2][0], fp[len(fp)//2][1])
            length = sum(distance_km(fp[i][0], fp[i][1], fp[i+1][0], fp[i+1][1]) for i in range(len(fp)-1))
            final_ways.append({'name': way['name'], 'type': way['type'], 'points': fp, 'avg_dist': avg_dist, 'direction': direction, 'length_km': length})

    final_ways.sort(key=lambda w: (0 if w['type'] == 'trail' else 1, w['avg_dist']))

    corridors = []
    for i, way in enumerate(final_ways):
        polygon = build_corridor_polygon(way['points'], offset_m)
        if polygon:
            corridors.append({
                'label': f'Corridor-{i+1:02d}',
                'trail_name': way['name'],
                'direction': way['direction'],
                'type': way['type'],
                'length_km': way['length_km'],
                'avg_dist_km': round(way['avg_dist'], 2),
                'polygon': polygon
            })
    return corridors

# --- File parsers ---

def parse_kml_trails(file_content):
    nodes = []
    try:
        root = etree.fromstring(file_content)
        for ce in root.iter('{http://www.opengis.net/kml/2.2}coordinates'):
            ct = ce.text
            if not ct: continue
            parent = ce.getparent()
            pt = parent.tag.split('}')[-1] if '}' in parent.tag else parent.tag
            if pt == 'LinearRing':
                gp = parent.getparent()
                gt = gp.tag.split('}')[-1] if '}' in gp.tag else gp.tag
                if gt in ['outerBoundaryIs', 'innerBoundaryIs']: continue
            for coord in ct.strip().split():
                parts = coord.split(',')
                if len(parts) >= 2:
                    try: nodes.append({'lat': float(parts[1]), 'lon': float(parts[0]), 'type': 'trail', 'weight': 2.0})
                    except ValueError: continue
    except Exception as e: print(f"KML parse error: {e}")
    return nodes

def parse_gpx_trails(file_content):
    nodes = []
    try:
        root = etree.fromstring(file_content)
        for trkpt in root.iter('{http://www.topografix.com/GPX/1/1}trkpt'):
            try: nodes.append({'lat': float(trkpt.get('lat')), 'lon': float(trkpt.get('lon')), 'type': 'trail', 'weight': 2.0})
            except: continue
        for rtept in root.iter('{http://www.topografix.com/GPX/1/1}rtept'):
            try: nodes.append({'lat': float(rtept.get('lat')), 'lon': float(rtept.get('lon')), 'type': 'trail', 'weight': 2.0})
            except: continue
    except Exception as e: print(f"GPX parse error: {e}")
    return nodes

def filter_trail_nodes_by_radius(trail_nodes, center_lat, center_lon, radius_km):
    return [n for n in trail_nodes if distance_km(center_lat, center_lon, n['lat'], n['lon']) <= radius_km]

# --- Terrain data ---

# --- Weather (Open-Meteo, no API key, free for non-commercial use) ---

WEATHER_CODES = {
    0: 'Clear sky', 1: 'Mainly clear', 2: 'Partly cloudy', 3: 'Overcast',
    45: 'Fog', 48: 'Depositing rime fog',
    51: 'Light drizzle', 53: 'Moderate drizzle', 55: 'Dense drizzle',
    56: 'Light freezing drizzle', 57: 'Dense freezing drizzle',
    61: 'Slight rain', 63: 'Moderate rain', 65: 'Heavy rain',
    66: 'Light freezing rain', 67: 'Heavy freezing rain',
    71: 'Slight snow', 73: 'Moderate snow', 75: 'Heavy snow', 77: 'Snow grains',
    80: 'Slight rain showers', 81: 'Moderate rain showers', 82: 'Violent rain showers',
    85: 'Slight snow showers', 86: 'Heavy snow showers',
    95: 'Thunderstorm', 96: 'Thunderstorm w/ slight hail', 99: 'Thunderstorm w/ heavy hail'
}

def deg_to_compass(deg):
    if deg is None: return ''
    dirs = ['N', 'NNE', 'NE', 'ENE', 'E', 'ESE', 'SE', 'SSE', 'S', 'SSW', 'SW', 'WSW', 'W', 'WNW', 'NW', 'NNW']
    return dirs[int((deg % 360) / 22.5 + 0.5) % 16]

def fetch_current_weather(lat, lon, units='standard'):
    """Fetch current weather + short forecast from Open-Meteo. Returns a dict or None on failure."""
    temp_unit = 'fahrenheit' if units == 'standard' else 'celsius'
    wind_unit = 'mph' if units == 'standard' else 'kmh'
    precip_unit = 'inch' if units == 'standard' else 'mm'
    url = 'https://api.open-meteo.com/v1/forecast'
    params = {
        'latitude': lat, 'longitude': lon,
        'current': 'temperature_2m,relative_humidity_2m,apparent_temperature,precipitation,weather_code,wind_speed_10m,wind_direction_10m,wind_gusts_10m',
        'daily': 'weather_code,temperature_2m_max,temperature_2m_min,precipitation_sum,precipitation_probability_max,wind_speed_10m_max,wind_gusts_10m_max,sunrise,sunset',
        'temperature_unit': temp_unit,
        'wind_speed_unit': wind_unit,
        'precipitation_unit': precip_unit,
        'forecast_days': 1,
        'timezone': 'auto'
    }
    try:
        r = requests.get(url, params=params, timeout=10)
        if r.status_code != 200: return None
        data = r.json()
        cur = data.get('current', {})
        if not cur: return None
        # Parse daily forecast (3 days returned)
        daily_raw = data.get('daily', {})
        forecast = []
        if daily_raw and daily_raw.get('time'):
            for i in range(len(daily_raw['time'])):
                forecast.append({
                    'date': daily_raw['time'][i],
                    'code': (daily_raw.get('weather_code') or [None]*99)[i],
                    'conditions': WEATHER_CODES.get((daily_raw.get('weather_code') or [None]*99)[i], 'Unknown'),
                    'high': (daily_raw.get('temperature_2m_max') or [None]*99)[i],
                    'low': (daily_raw.get('temperature_2m_min') or [None]*99)[i],
                    'precip_sum': (daily_raw.get('precipitation_sum') or [None]*99)[i],
                    'precip_prob': (daily_raw.get('precipitation_probability_max') or [None]*99)[i],
                    'wind_max': (daily_raw.get('wind_speed_10m_max') or [None]*99)[i],
                    'gust_max': (daily_raw.get('wind_gusts_10m_max') or [None]*99)[i],
                    'sunrise': (daily_raw.get('sunrise') or [None]*99)[i],
                    'sunset': (daily_raw.get('sunset') or [None]*99)[i],
                })
        return {
            'temp': cur.get('temperature_2m'),
            'feels_like': cur.get('apparent_temperature'),
            'humidity': cur.get('relative_humidity_2m'),
            'precip': cur.get('precipitation'),
            'wind_speed': cur.get('wind_speed_10m'),
            'wind_dir_deg': cur.get('wind_direction_10m'),
            'wind_dir_compass': deg_to_compass(cur.get('wind_direction_10m')),
            'wind_gust': cur.get('wind_gusts_10m'),
            'weather_code': cur.get('weather_code'),
            'conditions': WEATHER_CODES.get(cur.get('weather_code'), 'Unknown'),
            'time': cur.get('time'),
            'temp_unit': '°F' if units == 'standard' else '°C',
            'wind_unit': 'mph' if units == 'standard' else 'km/h',
            'precip_unit': 'in' if units == 'standard' else 'mm',
            'forecast': forecast
        }
    except Exception as e:
        print(f"Weather fetch error: {e}")
        return None

def format_weather_description(w):
    """Format a weather dict (current + forecast) into a human-readable description for the KML marker."""
    if not w: return 'Weather data unavailable'
    lines = []
    lines.append('=== CURRENT CONDITIONS ===')
    lines.append(f"Conditions: {w['conditions']}")
    if w.get('temp') is not None:
        line = f"Temperature: {w['temp']}{w['temp_unit']}"
        if w.get('feels_like') is not None:
            line += f" (feels like {w['feels_like']}{w['temp_unit']})"
        lines.append(line)
    if w.get('humidity') is not None:
        lines.append(f"Humidity: {w['humidity']}%")
    if w.get('wind_speed') is not None:
        line = f"Wind: {w['wind_speed']} {w['wind_unit']}"
        if w.get('wind_dir_compass'):
            line += f" from {w['wind_dir_compass']}"
        if w.get('wind_gust') is not None:
            line += f" (gusts to {w['wind_gust']} {w['wind_unit']})"
        lines.append(line)
    if w.get('precip') is not None and w['precip'] > 0:
        lines.append(f"Precipitation: {w['precip']} {w['precip_unit']}")
    if w.get('time'):
        lines.append(f"Observed: {w['time']}")

    # Forecast section (today only)
    forecast = w.get('forecast') or []
    if forecast:
        day = forecast[0]
        lines.append('')
        lines.append('=== TODAY\'S FORECAST ===')
        lines.append(f"Conditions: {day.get('conditions','')}")
        if day.get('high') is not None and day.get('low') is not None:
            lines.append(f"High: {day['high']}{w['temp_unit']}  /  Low: {day['low']}{w['temp_unit']}")
        if day.get('precip_prob') is not None or day.get('precip_sum') is not None:
            p_parts = []
            if day.get('precip_prob') is not None: p_parts.append(f"{day['precip_prob']}% chance")
            if day.get('precip_sum') is not None and day['precip_sum'] > 0: p_parts.append(f"{day['precip_sum']} {w['precip_unit']} total")
            if p_parts: lines.append(f"Precip: {' / '.join(p_parts)}")
        if day.get('wind_max') is not None:
            w_line = f"Wind max: {day['wind_max']} {w['wind_unit']}"
            if day.get('gust_max') is not None: w_line += f" (gusts {day['gust_max']} {w['wind_unit']})"
            lines.append(w_line)
        if day.get('sunrise') and day.get('sunset'):
            sr = day['sunrise'].split('T')[-1][:5] if 'T' in str(day['sunrise']) else day['sunrise']
            ss = day['sunset'].split('T')[-1][:5] if 'T' in str(day['sunset']) else day['sunset']
            lines.append(f"Sunrise: {sr}  Sunset: {ss}")

    lines.append('')
    lines.append('Source: Open-Meteo')
    return '\n'.join(lines)

def fetch_trail_data(lat, lon, radius_km):
    rm = int(radius_km * 1000)
    query = '[out:json][timeout:30];(way["highway"~"path|track|footway|bridleway|cycleway"](around:' + str(rm) + ',' + str(lat) + ',' + str(lon) + ');way["highway"~"residential|tertiary|secondary|primary|unclassified|service"](around:' + str(rm) + ',' + str(lat) + ',' + str(lon) + '););out body;>;out skel qt;'
    try:
        for server in ['https://overpass-api.de/api/interpreter', 'https://overpass.kumi.systems/api/interpreter']:
            try:
                r = requests.post(server, data={'data': query}, headers={'Accept': 'application/json', 'User-Agent': 'MARLY/1.0'}, timeout=30)
                if r.status_code == 200: break
            except: continue
        else: return [], []
        if r.status_code != 200: return [], []
        data = r.json()
        nodes = {}; trail_nodes = []; ways = []
        for el in data.get('elements', []):
            if el['type'] == 'node': nodes[el['id']] = (el['lat'], el['lon'])
        for el in data.get('elements', []):
            if el['type'] == 'way':
                ht = el.get('tags', {}).get('highway', '')
                is_trail = ht in ['path', 'track', 'footway', 'bridleway', 'cycleway']
                wn = el.get('tags', {}).get('name', f'Trail-{el["id"]}')
                wp = []
                for nid in el.get('nodes', []):
                    if nid in nodes:
                        nl, no = nodes[nid]
                        trail_nodes.append({'lat': nl, 'lon': no, 'type': 'trail' if is_trail else 'road', 'weight': 2.0 if is_trail else 1.0})
                        wp.append((nl, no))
                if wp: ways.append({'name': wn, 'type': 'trail' if is_trail else 'road', 'points': wp})
        return trail_nodes, ways
    except Exception as e:
        print(f"Overpass error: {e}")
        return [], []

def calculate_terrain_weights_grid(trail_nodes, center_lat, center_lon, outer_km, grid_cell_km):
    lo = km_to_lat(outer_km); lo2 = km_to_lon(outer_km, center_lat)
    cl = km_to_lat(grid_cell_km); co = km_to_lon(grid_cell_km, center_lat)
    cc = {}
    for n in trail_nodes:
        row = int((n['lat'] - (center_lat - lo)) / cl)
        col = int((n['lon'] - (center_lon - lo2)) / co)
        cc[(row, col)] = cc.get((row, col), 0) + n['weight']
    return cc

def apply_terrain_multiplier(bw, tc, mc):
    if mc == 0: return bw
    return round(bw * (1.0 + 0.5 * tc / mc), 2)

# --- Direction parsing ---

def parse_travel_direction(notes):
    direction_keywords = {'north': 'N', 'northeast': 'NE', 'east': 'E', 'southeast': 'SE', 'south': 'S', 'southwest': 'SW', 'west': 'W', 'northwest': 'NW'}
    notes_lower = notes.lower()
    for kw, b in direction_keywords.items():
        if kw in notes_lower: return b
    return None

# --- KML helpers ---

def coords_to_kml_string(points):
    return ' '.join(f'{lon:.6f},{lat:.6f},0' for lat, lon in points)

def add_kml_polygon(parent, name, desc, points, weight=1.0, zone='primary'):
    pm = etree.SubElement(parent, 'Placemark')
    etree.SubElement(pm, 'name').text = name
    etree.SubElement(pm, 'description').text = desc
    ss = etree.SubElement(pm, 'Style')
    sl = etree.SubElement(ss, 'LineStyle')
    sp = etree.SubElement(ss, 'PolyStyle')
    if zone == 'alternate':
        etree.SubElement(sl, 'color').text = 'FF00AAFF'  # Orange outline
        etree.SubElement(sl, 'width').text = '2.0'
        etree.SubElement(sp, 'color').text = '4400AAFF'  # Light orange fill
    elif weight > 1.0:
        etree.SubElement(sl, 'color').text = 'FF0000ff'
        etree.SubElement(sl, 'width').text = '2.0'
        etree.SubElement(sp, 'color').text = '1A0000ff'
    else:
        etree.SubElement(sl, 'color').text = 'FF333333'
        etree.SubElement(sl, 'width').text = '2.0'
        etree.SubElement(sp, 'color').text = '00000000'
    poly = etree.SubElement(pm, 'Polygon')
    etree.SubElement(poly, 'tessellate').text = '1'
    ob = etree.SubElement(poly, 'outerBoundaryIs')
    lr = etree.SubElement(ob, 'LinearRing')
    etree.SubElement(lr, 'coordinates').text = coords_to_kml_string(points)

# --- Main KML builder ---

def build_combined_kml(lat, lon, selected_rings, sector_data_all, markers=None, sector_shape='grid', grid_cell_km=None, max_sector_sq_km=None, corridors=None):
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
            if m.get('notes'): etree.SubElement(pm, 'description').text = m['notes']
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

    # Trail/Road corridors
    if corridors:
        cf = etree.SubElement(doc, 'Folder')
        etree.SubElement(cf, 'open').text = '1'
        etree.SubElement(cf, 'name').text = 'Trail/Road Corridors'
        for c in corridors:
            pm = etree.SubElement(cf, 'Placemark')
            etree.SubElement(pm, 'name').text = c['label']
            etree.SubElement(pm, 'description').text = f'{c["trail_name"]} - {c["direction"]} - {c["type"]}'
            cs = etree.SubElement(pm, 'Style')
            cl2 = etree.SubElement(cs, 'LineStyle')
            etree.SubElement(cl2, 'color').text = 'FF00AAFF'
            etree.SubElement(cl2, 'width').text = '2.0'
            cp = etree.SubElement(cs, 'PolyStyle')
            etree.SubElement(cp, 'color').text = '5500AAFF'
            poly = etree.SubElement(pm, 'Polygon')
            etree.SubElement(poly, 'tessellate').text = '1'
            ob = etree.SubElement(poly, 'outerBoundaryIs')
            lr = etree.SubElement(ob, 'LinearRing')
            etree.SubElement(lr, 'coordinates').text = coords_to_kml_string(c['polygon'])

    # Sectors
    for ring_data in sector_data_all:
        folder = etree.SubElement(doc, 'Folder')
        etree.SubElement(folder, 'name').text = ring_data['ring_label']
        inner_km, outer_km = ring_data['inner_km'], ring_data['outer_km']

        if sector_shape == 'grid':
            cell_km = float(grid_cell_km) if grid_cell_km else 0.35
            full_outer = selected_rings[-1]['km']
            lo = km_to_lat(full_outer); lo2 = km_to_lon(full_outer, lat)
            cld = km_to_lat(cell_km); cod = km_to_lon(cell_km, lat)
            for s in ring_data['sectors']:
                row, col = s.get('grid_row', 0), s.get('grid_col', 0)
                ml = (lat - lo) + row * cld; mo = (lon - lo2) + col * cod
                corners = [(ml, mo), (ml+cld, mo), (ml+cld, mo+cod), (ml, mo+cod), (ml, mo)]
                zone = s.get('zone', 'primary')
                add_kml_polygon(folder, f'{s["label"]} ({s["direction"]} Wt:{s["weight"]} {zone})', f'{ring_data["ring_label"]} - {zone}', corners, s['weight'], zone)
        else:
            sn = ['N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW']
            ba = [0, 45, 90, 135, 180, 225, 270, 315]
            for name, base_angle in zip(sn, ba):
                matching = [s for s in ring_data['sectors'] if s['direction'] == name]
                area = sector_area_sq_km(inner_km, outer_km, 45)
                if max_sector_sq_km and area > float(max_sector_sq_km):
                    sub_span = 45 / len(matching) if matching else 45
                    for si, sector in enumerate(matching):
                        sa = (base_angle - 22.5) + si * sub_span
                        ea = sa + sub_span
                        pts = sector_points(lat, lon, inner_km, outer_km, sa, ea)
                        zone = sector.get('zone', 'primary')
                        add_kml_polygon(folder, f'{sector["label"]} ({name} Wt:{sector["weight"]} {zone})', f'{ring_data["ring_label"]} - {zone}', pts, sector['weight'], zone)
                else:
                    sector = matching[0] if matching else None
                    if sector:
                        pts = sector_points(lat, lon, inner_km, outer_km, base_angle - 22.5, base_angle + 22.5)
                        zone = sector.get('zone', 'primary')
                        add_kml_polygon(folder, f'{sector["label"]} ({name} Wt:{sector["weight"]} {zone})', f'{ring_data["ring_label"]} - {zone}', pts, sector['weight'], zone)

    return etree.tostring(kml, pretty_print=True, xml_declaration=True, encoding='UTF-8')

# --- Hasty KML ---

def build_hasty_kml(lat, lon, ring_km, corridors, grid_sectors=None, markers=None):
    kml = etree.Element('kml', xmlns='http://www.opengis.net/kml/2.2')
    doc = etree.SubElement(kml, 'Document')
    etree.SubElement(doc, 'name').text = 'MARLY Hasty Search Plan'

    lkp_pm = etree.SubElement(doc, 'Placemark')
    ls = etree.SubElement(lkp_pm, 'Style')
    li = etree.SubElement(ls, 'IconStyle')
    etree.SubElement(li, 'hotSpot', x='0.5', xunits='fraction', y='0.5', yunits='fraction')
    lic = etree.SubElement(li, 'Icon')
    etree.SubElement(lic, 'href').text = LKP_ICON
    etree.SubElement(lkp_pm, 'name').text = 'Last Known Position'
    pt = etree.SubElement(lkp_pm, 'Point')
    etree.SubElement(pt, 'coordinates').text = f'{lon:.6f},{lat:.6f},0'

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
            if m.get('notes'): etree.SubElement(pm, 'description').text = m['notes']
            p = etree.SubElement(pm, 'Point')
            etree.SubElement(p, 'coordinates').text = f'{m["lon"]:.6f},{m["lat"]:.6f},0'

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

    cf = etree.SubElement(doc, 'Folder')
    etree.SubElement(cf, 'open').text = '1'
    etree.SubElement(cf, 'name').text = 'Trail Corridors'
    for c in corridors:
        pm = etree.SubElement(cf, 'Placemark')
        etree.SubElement(pm, 'name').text = c['label']
        etree.SubElement(pm, 'description').text = f'{c["trail_name"]} - {c["direction"]}'
        cs = etree.SubElement(pm, 'Style')
        cl2 = etree.SubElement(cs, 'LineStyle')
        etree.SubElement(cl2, 'color').text = 'FF00AAFF'
        etree.SubElement(cl2, 'width').text = '2.0'
        cp = etree.SubElement(cs, 'PolyStyle')
        etree.SubElement(cp, 'color').text = '5500AAFF'
        poly = etree.SubElement(pm, 'Polygon')
        etree.SubElement(poly, 'tessellate').text = '1'
        ob = etree.SubElement(poly, 'outerBoundaryIs')
        lr = etree.SubElement(ob, 'LinearRing')
        etree.SubElement(lr, 'coordinates').text = coords_to_kml_string(c['polygon'])

    if grid_sectors:
        sf = etree.SubElement(doc, 'Folder')
        etree.SubElement(sf, 'open').text = '1'
        etree.SubElement(sf, 'name').text = 'Hasty Search Sectors'
        for s in grid_sectors:
            zone = s.get('zone', 'primary')
            add_kml_polygon(sf, s['label'], f'{s["direction"]} - {s["area_acres"]:.0f} acres - {zone}', s['corners'], 1.0, zone)

    return etree.tostring(kml, pretty_print=True, xml_declaration=True, encoding='UTF-8')

# --- Routes ---

@app.route('/')
def index(): return render_template('form.html')

@app.route('/hasty')
def hasty(): return render_template('hasty.html')

@app.route('/submit', methods=['POST'])
def submit_form():
    data = request.json
    with open('search_plans.json', 'a') as f:
        f.write(json.dumps({'timestamp': datetime.now().isoformat(), **{k: data.get(k) for k in ['subject_type','latitude','longitude','time_last_seen','age','terrain','notes']}}) + '\n')
    return jsonify({'success': True})

@app.route('/upload-trail-file', methods=['POST'])
def upload_trail_file():
    global uploaded_trail_data
    if 'trail_file' not in request.files: return jsonify({'success': False, 'error': 'No file'})
    file = request.files['trail_file']
    if file.filename == '': return jsonify({'success': False, 'error': 'No file selected'})
    fn = secure_filename(file.filename); content = file.read(); ext = fn.lower().split('.')[-1]
    nodes = parse_kml_trails(content) if ext == 'kml' else parse_gpx_trails(content) if ext == 'gpx' else []
    if not nodes and ext not in ['kml', 'gpx']: return jsonify({'success': False, 'error': 'Use .kml or .gpx'})
    uploaded_trail_data = {'nodes': nodes, 'filename': fn}
    return jsonify({'success': True, 'filename': fn, 'total_nodes': len(nodes)})

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
    notes = data.get('notes', '')
    offset_m = float(data.get('offset_meters', 30))
    ring_pct = data.get('ring_pct', '50')
    sector_size_acres = float(data.get('sector_size_acres', 30))

    profile = SUBJECT_PROFILES.get(subject_type, {})
    ring_km = profile.get(f'ring_{ring_pct}_km', 2.0)
    custom_km = data.get('custom_ring_km')
    if custom_km: ring_km = float(custom_km)

    trail_nodes, ways = fetch_trail_data(lat, lon, ring_km)
    merged_ways = merge_connected_ways(ways, min_dead_end_m=50)

    # Get direction and template
    travel_direction = parse_travel_direction(notes)
    template = SECTOR_TEMPLATES.get(subject_type, {'primary_half_width': 180, 'alternate_half_width': 0, 'requires_direction': False})
    direction_angle = DIRECTION_ANGLES.get(travel_direction, 0) if travel_direction else None

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
            for p in way['points']: corridor_trail_nodes.add((round(p[0], 5), round(p[1], 5)))

    # Grid sectors for gaps with cone filtering
    sector_size_sqkm = sector_size_acres * ACRES_TO_SQKM
    cell_km = math.sqrt(sector_size_sqkm)
    lat_offset = km_to_lat(ring_km); lon_offset = km_to_lon(ring_km, lat)
    cell_lat = km_to_lat(cell_km); cell_lon = km_to_lon(cell_km, lat)

    grid_sectors = []
    sector_num = 1
    curr_lat = lat - lat_offset
    while curr_lat < lat + lat_offset:
        curr_lon = lon - lon_offset
        while curr_lon < lon + lon_offset:
            cl = curr_lat + cell_lat / 2; co = curr_lon + cell_lon / 2
            dist = distance_km(lat, lon, cl, co)
            # Detect cell containing the LKP/ring center
            contains_lkp = (curr_lat <= lat < curr_lat + cell_lat) and (curr_lon <= lon < curr_lon + cell_lon)
            if dist <= ring_km or contains_lkp:
                cell_has_trail = any(curr_lat <= tn[0] <= curr_lat + cell_lat and curr_lon <= tn[1] <= curr_lon + cell_lon for tn in corridor_trail_nodes)
                if not cell_has_trail:
                    direction = bearing_from_center(lat, lon, cl, co) if dist > 0 else 'N'
                    ba = bearing_angle(lat, lon, cl, co) if dist > 0 else 0
                    # Apply cone filter
                    if direction_angle is not None and template['requires_direction']:
                        zone = classify_sector_zone(ba, direction_angle, template)
                    else:
                        zone = 'primary'
                    # LKP cell is always primary, never filtered by cone
                    if contains_lkp:
                        zone = 'primary'
                    if zone != 'outside':
                        corners = [(curr_lat, curr_lon), (curr_lat+cell_lat, curr_lon), (curr_lat+cell_lat, curr_lon+cell_lon), (curr_lat, curr_lon+cell_lon), (curr_lat, curr_lon)]
                        grid_sectors.append({'label': f'HS-{sector_num:02d}', 'direction': direction, 'area_acres': sector_size_acres, 'area_sq_km': round(sector_size_sqkm, 3), 'dist_km': round(dist, 2), 'corners': corners, 'zone': zone, 'is_lkp': contains_lkp})
                        sector_num += 1
            curr_lon += cell_lon
        curr_lat += cell_lat

    grid_sectors.sort(key=lambda s: (0 if s.get('is_lkp') else 1, 0 if s['zone'] == 'primary' else 1, s['dist_km']))
    for i, s in enumerate(grid_sectors): s['label'] = f'HS-{i+1:02d}'

    cone_info = None
    if direction_angle is not None and template['requires_direction']:
        cone_info = {'direction': travel_direction, 'primary_width': template['primary_half_width'] * 2, 'alternate_width': (template['alternate_half_width'] - template['primary_half_width']) * 2 if template['alternate_half_width'] > 0 else 0}

    return jsonify({
        'success': True, 'ring_km': ring_km, 'ring_mi': round(ring_km / MI_TO_KM, 2),
        'total_ways': len(ways), 'merged_ways': len(merged_ways), 'corridors': len(corridors),
        'grid_sectors': len(grid_sectors), 'sector_size_acres': sector_size_acres,
        'cone_info': cone_info,
        'corridor_list': [{'label': c['label'], 'trail_name': c['trail_name'], 'direction': c['direction'], 'type': c['type'], 'length_km': round(c['length_km'], 2), 'length_mi': round(c['length_km']/MI_TO_KM, 2), 'avg_dist_km': c['avg_dist_km']} for c in corridors],
        'sector_list': [{'label': s['label'], 'direction': s['direction'], 'area_acres': s['area_acres'], 'dist_km': s['dist_km'], 'zone': s['zone']} for s in grid_sectors],
    })

@app.route('/download-hasty', methods=['POST'])
def download_hasty():
    data = request.json
    lat, lon = float(data['latitude']), float(data['longitude'])
    subject_type = data.get('subject_type')
    notes = data.get('notes', '')
    offset_m = float(data.get('offset_meters', 30))
    ring_pct = data.get('ring_pct', '50')
    sector_size_acres = float(data.get('sector_size_acres', 30))

    profile = SUBJECT_PROFILES.get(subject_type, {})
    ring_km = profile.get(f'ring_{ring_pct}_km', 2.0)
    custom_km = data.get('custom_ring_km')
    if custom_km: ring_km = float(custom_km)

    travel_direction = parse_travel_direction(notes)
    template = SECTOR_TEMPLATES.get(subject_type, {'primary_half_width': 180, 'alternate_half_width': 0, 'requires_direction': False})
    direction_angle = DIRECTION_ANGLES.get(travel_direction, 0) if travel_direction else None

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

    corridors = []; corridor_trail_nodes = set()
    for i, way in enumerate(final_ways):
        polygon = build_corridor_polygon(way['points'], offset_m)
        if polygon:
            corridors.append({'label': f'Hasty-{i+1:02d}', 'trail_name': way['name'], 'direction': way['direction'], 'length_km': way['length_km'], 'polygon': polygon})
            for p in way['points']: corridor_trail_nodes.add((round(p[0], 5), round(p[1], 5)))

    sector_size_sqkm = sector_size_acres * ACRES_TO_SQKM
    cell_km = math.sqrt(sector_size_sqkm)
    lat_offset = km_to_lat(ring_km); lon_offset = km_to_lon(ring_km, lat)
    cell_lat = km_to_lat(cell_km); cell_lon = km_to_lon(cell_km, lat)

    grid_sectors = []; sn = 1; curr_lat = lat - lat_offset
    while curr_lat < lat + lat_offset:
        curr_lon = lon - lon_offset
        while curr_lon < lon + lon_offset:
            cl = curr_lat + cell_lat / 2; co = curr_lon + cell_lon / 2
            dist = distance_km(lat, lon, cl, co)
            contains_lkp = (curr_lat <= lat < curr_lat + cell_lat) and (curr_lon <= lon < curr_lon + cell_lon)
            if dist <= ring_km or contains_lkp:
                cell_has_trail = any(curr_lat <= tn[0] <= curr_lat + cell_lat and curr_lon <= tn[1] <= curr_lon + cell_lon for tn in corridor_trail_nodes)
                if not cell_has_trail:
                    direction = bearing_from_center(lat, lon, cl, co) if dist > 0 else 'N'
                    ba = bearing_angle(lat, lon, cl, co) if dist > 0 else 0
                    zone = classify_sector_zone(ba, direction_angle, template) if direction_angle is not None and template['requires_direction'] else 'primary'
                    if contains_lkp:
                        zone = 'primary'
                    if zone != 'outside':
                        corners = [(curr_lat, curr_lon), (curr_lat+cell_lat, curr_lon), (curr_lat+cell_lat, curr_lon+cell_lon), (curr_lat, curr_lon+cell_lon), (curr_lat, curr_lon)]
                        grid_sectors.append({'label': f'HS-{sn:02d}', 'direction': direction, 'area_acres': sector_size_acres, 'corners': corners, 'zone': zone, 'is_lkp': contains_lkp}); sn += 1
            curr_lon += cell_lon
        curr_lat += cell_lat

    grid_sectors.sort(key=lambda s: (0 if s.get('is_lkp') else 1, 0 if s['zone'] == 'primary' else 1, distance_km(lat, lon, s['corners'][0][0]+cell_lat/2, s['corners'][0][1]+cell_lon/2)))
    for i, s in enumerate(grid_sectors): s['label'] = f'HS-{i+1:02d}'

    markers_input = data.get('markers', [])
    processed_markers = []; di = 0
    weather_units = data.get('search_params', {}).get('units', 'standard')
    lkp_weather = None
    if any(m.get('type') == 'wx_weather' for m in markers_input):
        lkp_weather = fetch_current_weather(lat, lon, weather_units)
    for m in markers_input:
        mi = MARKER_TYPES.get(m['type'], {})
        mlat, mlon = m.get('lat'), m.get('lon')
        if mlat and mlon: mlat, mlon = float(mlat), float(mlon)
        else: mlat, mlon = default_marker_position(lat, lon, ring_km, di); di += 1
        notes = m.get('notes', '')
        if m['type'] == 'wx_weather':
            notes = (notes + '\n\n' if notes else '') + format_weather_description(lkp_weather)
        processed_markers.append({'lat': mlat, 'lon': mlon, 'name': mi.get('name', m['type']), 'type': m['type'], 'notes': notes})

    kml_data = build_hasty_kml(lat, lon, ring_km, corridors, grid_sectors, processed_markers)
    return Response(kml_data, mimetype='application/vnd.google-earth.kml+xml', headers={'Content-Disposition': 'attachment;filename=MARLY_hasty_search.kml'})

@app.route('/download-combined', methods=['POST'])
def download_combined():
    data = request.json
    lat, lon = float(data['latitude']), float(data['longitude'])
    params = data.get('search_params', {})
    zones = calculate_search_zones(lat, lon, data.get('subject_type'), data.get('notes', ''), params)

    markers_input = data.get('markers', [])
    third_ring_km = zones['selected_rings'][2]['km'] if len(zones['selected_rings']) > 2 else zones['selected_rings'][-1]['km']
    processed_markers = []; di = 0
    weather_units = params.get('units', 'standard')
    # Fetch weather once for the LKP if any Weather marker is present
    lkp_weather = None
    if any(m.get('type') == 'wx_weather' for m in markers_input):
        lkp_weather = fetch_current_weather(lat, lon, weather_units)
    for m in markers_input:
        mi = MARKER_TYPES.get(m['type'], {})
        mlat, mlon = m.get('lat'), m.get('lon')
        if mlat and mlon: mlat, mlon = float(mlat), float(mlon)
        else: mlat, mlon = default_marker_position(lat, lon, third_ring_km, di); di += 1
        notes = m.get('notes', '')
        # Weather marker: append current LKP weather to notes
        if m['type'] == 'wx_weather':
            notes = (notes + '\n\n' if notes else '') + format_weather_description(lkp_weather)
        processed_markers.append({'lat': mlat, 'lon': mlon, 'name': mi.get('name', m['type']), 'type': m['type'], 'notes': notes})

    kml_data = build_combined_kml(lat, lon, zones['selected_rings'], zones['sector_data_all'], markers=processed_markers, sector_shape=params.get('sector_shape', 'grid'), grid_cell_km=params.get('grid_cell_km'), max_sector_sq_km=params.get('max_sector_sq_km'), corridors=zones.get('corridors'))
    return Response(kml_data, mimetype='application/vnd.google-earth.kml+xml', headers={'Content-Disposition': 'attachment;filename=MARLY_search_plan.kml'})

# --- Core calculation ---

def calculate_search_zones(lat, lon, subject_type, notes, params):
    global uploaded_trail_data
    profile = SUBJECT_PROFILES.get(subject_type, {})
    ring_options = [{'key': 'ring_25', 'pct': 25, 'default_km': profile.get('ring_25_km', 1.0)}, {'key': 'ring_50', 'pct': 50, 'default_km': profile.get('ring_50_km', 2.0)}, {'key': 'ring_75', 'pct': 75, 'default_km': profile.get('ring_75_km', 4.0)}, {'key': 'ring_95', 'pct': 95, 'default_km': profile.get('ring_95_km', 8.0)}]
    selected_rings = []
    for ring in ring_options:
        if params.get(ring['key'], False):
            ckm = params.get(ring['key'] + '_km')
            selected_rings.append({'pct': ring['pct'], 'km': float(ckm) if ckm else ring['default_km']})
    if not selected_rings:
        selected_rings = [{'pct': 50, 'km': profile.get('ring_50_km', 2.0)}, {'pct': 95, 'km': profile.get('ring_95_km', 8.0)}]
    selected_rings.sort(key=lambda r: r['km'])

    travel_direction = parse_travel_direction(notes)
    template = SECTOR_TEMPLATES.get(subject_type, {'primary_half_width': 180, 'alternate_half_width': 0, 'requires_direction': False})
    direction_angle_val = DIRECTION_ANGLES.get(travel_direction, 0) if travel_direction else None

    sector_weights = {}
    for sector in ['N', 'NE', 'E', 'SE', 'S', 'SW', 'W', 'NW']:
        w = 1.0
        if subject_type == 'dementia' and travel_direction == sector: w *= 1.5
        elif travel_direction == sector: w *= 1.3
        sector_weights[sector] = round(w, 1)

    terrain_aware = params.get('terrain_aware', False)
    terrain_source = params.get('terrain_source', 'osm')
    corridor_enabled = params.get('corridor_enabled', False)
    trail_nodes = []; ways_data = []; terrain_stats = {}
    outer_km_full = selected_rings[-1]['km']
    if terrain_aware or corridor_enabled:
        if terrain_aware and terrain_source == 'file' and uploaded_trail_data['nodes']:
            trail_nodes = filter_trail_nodes_by_radius(uploaded_trail_data['nodes'], lat, lon, outer_km_full)
            terrain_stats = {'source': 'file', 'filename': uploaded_trail_data['filename'], 'total_nodes': len(trail_nodes), 'trail_nodes': len(trail_nodes), 'road_nodes': 0}
            # File source has no way data - fetch OSM separately if corridors needed
            if corridor_enabled:
                _, ways_data = fetch_trail_data(lat, lon, outer_km_full)
        else:
            tn, ways_data = fetch_trail_data(lat, lon, outer_km_full)
            trail_nodes = tn
            if terrain_aware:
                terrain_stats = {'source': 'osm', 'total_nodes': len(trail_nodes), 'trail_nodes': len([n for n in trail_nodes if n['type'] == 'trail']), 'road_nodes': len([n for n in trail_nodes if n['type'] == 'road'])}

    corridors_list = []
    if corridor_enabled and ways_data:
        corridor_offset_m = float(params.get('corridor_offset_m', 30))
        corridor_feature_type = params.get('corridor_feature_type', 'both')
        corridors_list = build_corridors_from_data(lat, lon, outer_km_full, ways_data, corridor_offset_m, corridor_feature_type)

        # Per-ring corridor filter: classify each corridor by which ring its avg distance falls into,
        # then drop it if the user unchecked Corridors for that ring.
        if corridors_list:
            filtered = []
            for c in corridors_list:
                d = c['avg_dist_km']
                ring_pct_for_corridor = None
                prev_radius = 0
                for r in selected_rings:
                    if prev_radius < d <= r['km']:
                        ring_pct_for_corridor = r['pct']
                        break
                    prev_radius = r['km']
                # Corridor inside the innermost ring or past the outermost
                if ring_pct_for_corridor is None:
                    ring_pct_for_corridor = selected_rings[0]['pct'] if d <= selected_rings[0]['km'] else selected_rings[-1]['pct']
                if params.get(f'corridors_{ring_pct_for_corridor}', True):
                    c['ring_pct'] = ring_pct_for_corridor
                    filtered.append(c)
            corridors_list = filtered

    sector_shape = params.get('sector_shape', 'grid')
    grid_cell_km = params.get('grid_cell_km')
    max_sector_sq_km = params.get('max_sector_sq_km')
    radii = [r['km'] for r in selected_rings]
    sector_data_all = []
    MAX_SECTORS_GLOBAL = 500
    total_sector_count = 0

    for i in range(len(selected_rings)):
        inner_km = radii[i-1] if i > 0 else 0
        outer_km = radii[i]
        pct = selected_rings[i]['pct']
        priority = i + 1
        ring_label = f'P{priority} ({pct}% ring)'

        # Per-ring sector toggle: only generate sectors if the user opted in for this ring.
        # Default True if param is missing (keeps API backward-compatible for older calls).
        sectors_enabled_for_ring = params.get(f'sectors_{pct}', True)

        # Skip sector generation for this ring if:
        #  - User unchecked "Sectors" for this specific ring, OR
        #  - This ring's percentile is > 75% (corridors-only zone per spec), OR
        #  - We've already hit the global 500-sector cap from inner rings
        skip_sectors = (not sectors_enabled_for_ring) or (pct > 75) or (total_sector_count >= MAX_SECTORS_GLOBAL)

        if skip_sectors:
            if not sectors_enabled_for_ring:
                skip_reason = 'sectors_off_this_ring'
            elif pct > 75:
                skip_reason = 'outer_band_75_95'
            else:
                skip_reason = 'capped_at_500'
            sector_data_all.append({'ring_label': ring_label, 'inner_km': inner_km, 'outer_km': outer_km, 'pct': pct, 'priority': priority, 'sectors': [], 'skipped': True, 'skip_reason': skip_reason})
            continue

        if sector_shape == 'grid':
            cell_km = float(grid_cell_km) if grid_cell_km else 0.35
            cell_area = cell_km * cell_km
            lo = km_to_lat(selected_rings[-1]['km']); lo2 = km_to_lon(selected_rings[-1]['km'], lat)
            cl = km_to_lat(cell_km); co = km_to_lon(cell_km, lat)
            gtc = calculate_terrain_weights_grid(trail_nodes, lat, lon, selected_rings[-1]['km'], cell_km) if terrain_aware and trail_nodes else {}
            mtc = max(gtc.values()) if gtc else 0
            cells = []
            curr_lat = lat - lo; row = 0
            while curr_lat < lat + lo:
                curr_lon = lon - lo2; col_idx = 0
                while curr_lon < lon + lo2:
                    ccl = curr_lat + cl/2; cco = curr_lon + co/2
                    dist = distance_km(lat, lon, ccl, cco)
                    # Detect cell containing the LKP/ring center - must always be included in ring 0
                    contains_lkp = (curr_lat <= lat < curr_lat + cl) and (curr_lon <= lon < curr_lon + co)
                    in_dist_range = inner_km < dist <= outer_km
                    # Force LKP cell into innermost ring (i==0) even if cone or dist would exclude it
                    if in_dist_range or (contains_lkp and i == 0):
                        d = bearing_from_center(lat, lon, ccl, cco) if dist > 0 else 'N'
                        ba = bearing_angle(lat, lon, ccl, cco) if dist > 0 else 0
                        # Cone filter
                        if direction_angle_val is not None and template['requires_direction']:
                            zone = classify_sector_zone(ba, direction_angle_val, template)
                        else:
                            zone = 'primary'
                        # LKP cell is always primary regardless of cone
                        if contains_lkp and i == 0:
                            zone = 'primary'
                        if zone != 'outside':
                            bw = sector_weights.get(d, 1.0)
                            tc = gtc.get((row, col_idx), 0)
                            w = apply_terrain_multiplier(bw, tc, mtc) if terrain_aware and mtc > 0 else bw
                            cells.append({'direction': d, 'weight': w, 'dist': round(dist, 2), 'area_sq_km': round(cell_area, 2), 'area_acres': round(cell_area / ACRES_TO_SQKM, 1), 'grid_row': row, 'grid_col': col_idx, 'trail_count': int(tc) if terrain_aware else None, 'zone': zone, 'is_lkp': contains_lkp and i == 0})
                    curr_lon += co; col_idx += 1
                curr_lat += cl; row += 1
            cells.sort(key=lambda c: (0 if c.get('is_lkp') else 1, 0 if c['zone'] == 'primary' else 1, c['dist']))
            # Truncate to fit within global 500-sector cap (counts across rings)
            remaining = MAX_SECTORS_GLOBAL - total_sector_count
            if len(cells) > remaining:
                cells = cells[:remaining]
            total_sector_count += len(cells)
            suffix = '' if i == 0 else chr(64+i)
            for j, cell in enumerate(cells):
                cell['label'] = f'Sector-{j+1:02d}{suffix}'
                cell['priority'] = priority
            sector_data_all.append({'ring_label': ring_label, 'inner_km': inner_km, 'outer_km': outer_km, 'pct': pct, 'priority': priority, 'sectors': cells})
        else:
            sector_span = 45
            area = sector_area_sq_km(inner_km, outer_km, sector_span)
            rtc = {s: 0.0 for s in ['N','NE','E','SE','S','SW','W','NW']}
            if terrain_aware and trail_nodes:
                for node in trail_nodes:
                    dist = distance_km(lat, lon, node['lat'], node['lon'])
                    if inner_km < dist <= outer_km:
                        rtc[bearing_from_center(lat, lon, node['lat'], node['lon'])] += node['weight']
            mt = max(rtc.values()) if any(rtc.values()) else 0
            pie_sectors = []; sn = 1; suffix = '' if i == 0 else chr(64+i)
            for sector in ['N','NE','E','SE','S','SW','W','NW']:
                sa = DIRECTION_ANGLES[sector]
                if direction_angle_val is not None and template['requires_direction']:
                    zone = classify_sector_zone(sa, direction_angle_val, template)
                else:
                    zone = 'primary'
                if zone == 'outside': continue
                bw = sector_weights[sector]; tc = rtc.get(sector, 0)
                w = apply_terrain_multiplier(bw, tc, mt) if terrain_aware and mt > 0 else bw
                subs = math.ceil(area / float(max_sector_sq_km)) if max_sector_sq_km and area > float(max_sector_sq_km) else 0
                if subs > 0:
                    for s in range(subs):
                        pie_sectors.append({'direction': sector, 'label': f'Sector-{sn:02d}{suffix}', 'priority': priority, 'weight': w, 'area_sq_km': round(area/subs, 2), 'area_acres': round((area/subs)/ACRES_TO_SQKM, 1), 'trail_count': int(tc) if terrain_aware else None, 'zone': zone}); sn += 1
                else:
                    pie_sectors.append({'direction': sector, 'label': f'Sector-{sn:02d}{suffix}', 'priority': priority, 'weight': w, 'area_sq_km': round(area, 2), 'area_acres': round(area/ACRES_TO_SQKM, 1), 'trail_count': int(tc) if terrain_aware else None, 'zone': zone}); sn += 1
            # Truncate to fit within global 500-sector cap
            remaining = MAX_SECTORS_GLOBAL - total_sector_count
            if len(pie_sectors) > remaining:
                pie_sectors = pie_sectors[:remaining]
            total_sector_count += len(pie_sectors)
            sector_data_all.append({'ring_label': ring_label, 'inner_km': inner_km, 'outer_km': outer_km, 'pct': pct, 'priority': priority, 'sectors': pie_sectors})

    cone_info = None
    if direction_angle_val is not None and template['requires_direction']:
        cone_info = {'direction': travel_direction, 'subject_type': subject_type, 'primary_width': template['primary_half_width'] * 2, 'alternate_width': (template['alternate_half_width'] - template['primary_half_width']) * 2 if template['alternate_half_width'] > 0 else 0}

    result = {'lat': lat, 'lon': lon, 'selected_rings': selected_rings, 'travel_direction': travel_direction, 'sector_shape': sector_shape, 'terrain_aware': terrain_aware, 'sector_data_all': sector_data_all, 'search_params': params, 'cone_info': cone_info, 'total_sectors': total_sector_count, 'sector_cap': MAX_SECTORS_GLOBAL}
    if terrain_aware: result['terrain_stats'] = terrain_stats
    if corridor_enabled:
        result['corridors'] = corridors_list
        result['corridor_list'] = [{'label': c['label'], 'trail_name': c['trail_name'], 'direction': c['direction'], 'type': c['type'], 'length_km': round(c['length_km'], 2), 'length_mi': round(c['length_km']/MI_TO_KM, 2), 'avg_dist_km': c['avg_dist_km'], 'ring_pct': c.get('ring_pct')} for c in corridors_list]
    return result

if __name__ == '__main__':
    import os
    port = int(os.environ.get('PORT', 5000))
    app.run(host='0.0.0.0', port=port, debug=False)
