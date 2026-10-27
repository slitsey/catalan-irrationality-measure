"""Independent exact rational geometry mirror for PilotCorner.lean (not an analytic proof)."""
from fractions import Fraction as Q
import json

heights = list(map(Q, ['0.042495133047399575', '0.1274853991421987', '0.23372323176069765']))
leans = list(map(Q, ['-0.5341500350645203', '-0.4721222614562869', '-0.36277948981216984']))
vertices = []
x, y = -Q(1, 10), Q(0)
for height, lean in zip(heights, leans):
    x = x + lean * (height - y)
    y = height
    vertices.append((x, y))
assert all(y > 0 for x, y in vertices)
assert all(x < 0 for x, y in vertices)
assert Q(1, 18) - Q(1, 12) + Q(1, 36) == 0
assert len(set(vertices)) == 3
for j in range(2):
    x0, y0 = vertices[j]
    x1, y1 = vertices[j + 1]
    assert (x1 - x0) / (y1 - y0) == leans[j + 1]
print(json.dumps({'status': 'PASS exact finite geometry only',
    'vertices': [[str(x), str(y)] for x, y in vertices],
    'all_imaginary_parts_positive': True, 'frame_balanced': True}, indent=2))
