<#
  T066 replay -- narrow, read-only source audit.

  Reproduces exactly one thing: that every source cited by source-audit.json
  and SUMMARY.md is present in this workspace at the SHA256 recorded there,
  that the upstream Lean checkout is still at the baseline commit with a
  clean worktree, and that the cited declarations are still at the cited
  lines.

  It does NOT run Lean, does NOT build, does NOT download, does NOT modify
  the main repository, the Boundary files or the fact-tree. It only reads
  files and prints to stdout.

  ASCII-only on purpose: Windows PowerShell 5.1 parses .ps1 as ANSI, and the
  repository root can contain non-ASCII characters. The root is therefore
  derived from this script's own location (delegated/2026-10-24/T066), not
  spelled out as a literal.

  Receiver: read this file first, then decide whether to run it.
  Usage:  powershell -NoProfile -ExecutionPolicy Bypass -File replay.ps1
#>
[CmdletBinding()]
param(
  [string]$Root
)

$ErrorActionPreference = 'Stop'

if (-not $Root) {
  # <root>/delegated/2026-10-24/T066 -> up three levels
  $Root = Split-Path -Parent (Split-Path -Parent (Split-Path -Parent $PSScriptRoot))
}

# path, expected sha256, expected bytes
$Pins = @(
  @('handoffs/agent-batch-2026-10-24/baseline.json',                          'e24e6801c2eac58f7d97cfe5f3f7a95deeaf05852231006a0085290eecd126cf', 20311),
  @('handoffs/agent-batch-2026-10-24/cards/T066.md',                          'e57fe2507b74b040958573c8982c494f6698323fc7129848bc0b8c31314d2d50',  2718),
  @('research/core-next-2026-10-23/native-source-square.md',                  '7859ec31035b9ddf64dd70c2a72846ab45143a3d812739082d385c9be9c24163',  6726),
  @('research/core-comparison-2026-10-24/GAP-shared-anchor-source.md',        '7c795ff18102f1809e9d564d7caa64f085bbae0a8f14f379b358329583c2cb8c',  1755),
  @('research/round2-source-cache/iut-II-official-retrieved-2026-10-23.txt',  '7d5b7bd7d4e53c4d96b1ed24a05dffa1f9a5fae539b1129a9a12f0b7665e7fab', 486892),
  @('research/round2-source-cache/iut-III-official-retrieved-2026-10-16.txt', '70a618ada5e5039b84283c21fc1b947db9dced559d46ecb2786e05ae6164b715', 570037),
  @('research/round2-source-cache/LANA-interim-report-2026-07.txt',           '5fc6185d6642e70ba58c6ce637ef6e0448e2761b9d57b5e40545aea3d6ee040e', 144233),
  @('reviews/core-round/external/iut/Iut/LogLink/Thm311Rest.lean',            '01d439345e489cc92be6e19db7e2b30a9a9536f788244aaa69a2066de3a69a2d',  34328),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/CyclotomicRigidity.lean', '69205310b880ecc3637b5951095d54c791dcc19450c1d0921171767d33a9152f',  18108),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/MonoTheta.lean',          'a9694735eaa0e55d76f4bd88c02bb8b78eb8230cf2b967b9ed45f68396a8ebd1',  13354),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/ArithEnv.lean',           '95ec45e061e07db5a463669579c595a8c3ff094d02f8843f8fc6bcb41cbad457',  10427),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/ModelAut.lean',           '4e56fee8a2ca13f065e0feba49170eae30f0ecfdc7e41ab472b7e583388646ef',  26435),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/ModelTower.lean',         '3bd3fce413f783c51a75b996f0e9f10979360bbf489a125da0c38a292976bb42',  15013),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/ThetaClass.lean',         'b89f8dc0987d002021a5259b06263e9c9d8414eb27073bb4c2bb75579e1fea79',   8740),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/TemperedCovering.lean',   '436df768ffa6c5657ad0d00759c885004b6ee963cf086d7b6e7f435945630ba8',  11861),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/TempSlimPiY.lean',        '5be36a1fedef755c38d01091ae4c69bcd9253e52f0301fcf7c6840b9085f249a',   4247),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/CyclotomicEnvelope.lean', '1ac98e3ac3f5bafeb69ddcd64b82c839022f3d8cef4db92ec0741a9ca567b394',  12946),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/RigidSystems.lean',       '31afb86bd6561e3ce416d5805c6652fbbe3dfa74f23f7ad9629d4bf92743b88b',   9698),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/README.md',               'd690abb46816166553e8bc163f85f32312611739697fb53d667dc8fa9fa446e1',  26064),
  @('reviews/core-round/external/iut/Iut/Frobenioid/Tempered.lean',           '3fb8b3da4bed2ae831e13aedf24eaf18527650e92232b6b15c53999cd91f3b2f',  18968),
  @('reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean',           'a7b091c5cd076112ce3ea1151dcc4137a81ebd2e4d746781ec36ada953368049',  12590),
  @('reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean',             '1dd1a56eff40a021f1de9835d7172706a6240495d7e27ef9cb1db7beec4f2e55',  22657),
  @('reviews/core-round/external/iut/Iut/LogLink/Kummer.lean',                'c250443ede2e12be428f7e84ec7b61aab82eab724a1134358152eccdb877e4e4',  15226),
  @('reviews/core-round/external/iut/Iut/LogLink/Lattice.lean',               '715a331ddf1846b9164edddcd668cc26aa28a259aad925a6ae05904992ee125f',   8047),
  @('reviews/core-round/external/iut/Iut/LogLink/Thm311LGP.lean',             '862eaed70b1588eaf198ae9114d9897d5811f73c4904bc2d56076103c1014aaf',  11358),
  @('reviews/core-round/external/iut/Iut/HodgeTheater/HodgeTheater.lean',     'b5c54b4f2fa563fbfc70e1270003dea59197733090a7dafcc316e7f31d64a387',  11032),
  @('reviews/core-round/external/iut/Iut/HodgeTheater/StripLift.lean',        'cd8fe6448d3a6d96e9988b38618ceefb0518baf6d0a93b8d73f261c229bd21b4',  26190),
  @('reviews/core-round/external/iut/Iut/HodgeTheater/FStarMod.lean',         '69abb16448fe0b9d42931f545c0ef033e6228d966ef56818f984e73deada395c',   6192),
  @('reviews/core-round/external/iut/Iut/Cor312/ThetaData/Basic.lean',        'c375bbf39ad8a5767637743d2efc7e73fab78fa0c8065b8d3ff18929cf4748f5',  14626),
  @('reviews/core-round/external/iut/Iut/WallEquiv/NonDerivable.lean',        'c6f0e46e5a5a4badd78792ad498b1bc05ebca3a92c4d78e0bdf3fb964bb4aca9',  27825),
  @('reviews/core-round/external/iut/README.md',                              'd00a19dcb22099bf9d219277b12845e4f92c879ea1387e20bd47ee2194f1d8cd',  85397),
  @('reviews/core-round/external/iut/Iut/WallEquiv/README.md',                '034a907afb395db70774a4b90d7e3db57e90b6f7e075dc678eb51f6d39205189',  20016)
)

# relpath, 1-based line, substring that must appear on that line
$Markers = @(
  @('reviews/core-round/external/iut/Iut/LogLink/Thm311Rest.lean',           270, 'structure MonoThetaKummer where'),
  @('reviews/core-round/external/iut/Iut/LogLink/Thm311Rest.lean',           286, 'variable (M : MonoThetaKummer D)'),
  @('reviews/core-round/external/iut/Iut/LogLink/Thm311Rest.lean',           290, 'def const (D : InitialThetaData'),
  @('reviews/core-round/external/iut/Iut/LogLink/Thm311Rest.lean',           316, 'theorem isCyc_horizMap'),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/CyclotomicRigidity.lean',  81, 'structure Env where'),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/CyclotomicRigidity.lean', 112, 'def IsCyc'),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/CyclotomicRigidity.lean', 227, 'abbrev model'),
  @('reviews/core-round/external/iut/Iut/EtaleTheta/CyclotomicRigidity.lean', 364, 'theorem cyclotomicRigidity'),
  @('reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean',          168, 'structure StripKummer')
)

function Get-Sha256([string]$Path) {
  (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
}

$fail = 0

Write-Output 'T066 REPLAY: source pin verification (read-only)'
Write-Output ('root = ' + $Root)
Write-Output ''

foreach ($pin in $Pins) {
  $rel       = [string]$pin[0]
  $want      = [string]$pin[1]
  $wantBytes = [int64]$pin[2]
  $abs       = Join-Path $Root ($rel -replace '/', '\')
  if (-not (Test-Path -LiteralPath $abs)) {
    Write-Output ('FAIL missing  ' + $rel)
    $fail++
    continue
  }
  $got      = Get-Sha256 $abs
  $gotBytes = (Get-Item -LiteralPath $abs).Length
  if ($got -eq $want -and $gotBytes -eq $wantBytes) {
    Write-Output ('PASS ' + $got + '  ' + $rel)
  } else {
    Write-Output ('FAIL ' + $got + '  ' + $rel + '  (want ' + $want + '; bytes ' + $gotBytes + '/' + $wantBytes + ')')
    $fail++
  }
}

Write-Output ''
$iut = Join-Path $Root 'reviews\core-round\external\iut'
if (Test-Path -LiteralPath (Join-Path $iut '.git')) {
  $wantHead = 'f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb'
  $head = (& git -C $iut rev-parse HEAD 2>$null)
  if ($head -eq $wantHead) {
    Write-Output ('PASS iut HEAD ' + $head)
  } else {
    Write-Output ('FAIL iut HEAD ' + $head + '  (want ' + $wantHead + ')')
    $fail++
  }
  $dirty = @(& git -C $iut status --porcelain 2>$null)
  if ($dirty.Count -eq 0) {
    Write-Output 'PASS iut worktree clean'
  } else {
    Write-Output ('FAIL iut worktree has ' + $dirty.Count + ' local modification(s)')
    $fail++
  }
} else {
  Write-Output ('SKIP upstream git identity (no .git at ' + $iut + ')')
}

Write-Output ''
foreach ($mk in $Markers) {
  $rel  = [string]$mk[0]
  $ln   = [int]$mk[1]
  $text = [string]$mk[2]
  $abs  = Join-Path $Root ($rel -replace '/', '\')
  if (-not (Test-Path -LiteralPath $abs)) {
    Write-Output ('FAIL missing  ' + $rel)
    $fail++
    continue
  }
  $line = (Get-Content -LiteralPath $abs -TotalCount $ln)[$ln - 1]
  if ($null -ne $line -and $line.Contains($text)) {
    Write-Output ('PASS L' + $ln + ' ' + $text + '   [' + (Split-Path $rel -Leaf) + ']')
  } else {
    Write-Output ('FAIL L' + $ln + ' does not contain "' + $text + '"   [' + $rel + ']')
    $fail++
  }
}

Write-Output ''
if ($fail -eq 0) {
  Write-Output 'RESULT: ALL_PINS_OK'
  exit 0
} else {
  Write-Output ('RESULT: PIN_MISMATCH count=' + $fail)
  exit 1
}
