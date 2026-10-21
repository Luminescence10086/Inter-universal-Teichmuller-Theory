import sys
import time

mode = sys.argv[1] if len(sys.argv) > 1 else 'ok'
if mode == 'ok':
    print('probe ok')
    raise SystemExit(0)
if mode == 'fail':
    print('probe fail', file=sys.stderr)
    raise SystemExit(1)
if mode == 'slow':
    time.sleep(5)
    print('probe slow finished')
    raise SystemExit(0)
print(f'unknown probe mode {mode!r}', file=sys.stderr)
raise SystemExit(2)
