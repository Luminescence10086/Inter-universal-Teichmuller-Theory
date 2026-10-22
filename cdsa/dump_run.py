import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2]))
from cdsa.core import EventLog

run = pathlib.Path(__file__).resolve().parents[2] / 'cdsa/runs/demo-01'
log = EventLog(run)
for line in log._lines():
    payload = line['payload']
    tag = payload.get('node') or payload.get('edge') or payload.get('goal')
    print(line['seq'], line['type'], str(tag)[:30], payload.get('color', ''))
state = log.replay()
print('admitted:', state['admitted'])
print('gates:', {k: v for k, v in state['gates'].items()})
print('chain:', log.verify_chain())
