"""Record the InfoView observations in the T3 receipt and delivery."""
import hashlib
import io
import json
import time
from pathlib import Path

ROOT = Path(r'D:\Inter-universal Teichmüller Theory')
T3 = ROOT / 'handoffs/core-support-2026-10-22/T3'
INFO = T3 / 'infoview'


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


OBS = {
    'localLog_eq_padicLog': {'line': 36, 'text': 'No goals'},
    'summable_logTerm': {'line': 41, 'text': 'Goals accomplished!'},
    'hasSum_logTerm_localLog': {'line': 50, 'text': 'No goals'},
    'logImage_Q3_eq_closedBall': {'line': 64, 'text': 'Goals accomplished!'},
}

receipt = json.load(io.open(T3 / 'vscode-receipt.json', encoding='utf-8'))
receipt['recorded_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
receipt['scope_of_the_check'] = (
    'zero error and zero warning diagnostics for candidates/core-transport/DelegatedLogBridge.lean '
    'in a trusted window with the Lean 4 extension active, plus a zero-goal InfoView reading at '
    'each of the four declarations')
receipt['infoview'] = {
    'observed': True,
    'zero_goals_meaning': ('"No goals" and "Goals accomplished!" are the two strings the Lean 4 '
                           'Tactic state section shows when the goal list is empty'),
    'method': ('VS Code relaunched with --force-renderer-accessibility so the embedded webview '
               'enters the accessibility tree; for each declaration the cursor was parked on the '
               'line after the last tactic step (or at the end of it); the text was then read '
               'from the Infoview Tactic state section, whose sibling section All Messages ( 4) '
               'holds the four axiom reports'),
    'per_declaration': OBS,
    'evidence': {name: 'infoview/%s.txt' % name for name in OBS},
    'flakiness_note': ('the pane does not always repaint immediately; the first passes read an '
                      'empty Tactic state, so the capture now polls up to 24 s for the text '
                      'instead of sleeping a fixed interval. The run recorded here is a single '
                      'pass in which all four were read.'),
}
receipt.pop('not_observed', None)
receipt['editor_status'] = 'EDITOR_CHECKED'
receipt['evidence'].update(
    {'infoview/%s.txt' % name: sha(INFO / ('%s.txt' % name)) for name in OBS})
receipt['evidence']['infoview/infoview-summary.json'] = sha(INFO / 'infoview-summary.json')
receipt['evidence']['capture-infoview.ps1'] = sha(T3 / 'capture-infoview.ps1')
(T3 / 'vscode-receipt.json').write_text(
    json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

delivery = json.load(io.open(T3 / 'delivery.json', encoding='utf-8'))
delivery['status'] = 'CLI_CHECKED_EDITOR_PENDING'
delivery['vocabulary_note'] = (
    'the closed status vocabulary has no value meaning "verified in both planes"; this value is '
    'the closest documented one, and editor_status = EDITOR_CHECKED carries the actual editor '
    'outcome, so nothing here should be read as the editor still being pending')
delivery['editor_status'] = 'EDITOR_CHECKED'
delivery['completed'].append(
    'InfoView zero-goal reading obtained in a single pass for all four declarations '
    '("No goals" or "Goals accomplished!") by relaunching with --force-renderer-accessibility and '
    'polling the Tactic state section')
delivery['open'] = [
    'candidates/core-transport/CoreTransport.lean is outside T3\'s permitted-source rule; it was '
    'authorised by the user on 2026-10-23 and is labelled as a structural fix in its header',
]
delivery['outputs'] = [
    {'path': str(p.relative_to(ROOT)).replace('\\', '/'), 'sha256': sha(p)}
    for p in sorted(T3.rglob('*')) if p.is_file() and p.name != 'delivery.json']
(T3 / 'delivery.json').write_text(
    json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

print('receipt infoview observed:', receipt['infoview']['observed'])
print('delivery status:', delivery['status'], '| editor:', delivery['editor_status'],
      '| outputs:', len(delivery['outputs']), '| open:', len(delivery['open']))
print('receipt sha256:', sha(T3 / 'vscode-receipt.json'))
