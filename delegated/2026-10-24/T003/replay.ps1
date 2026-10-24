# T003 replay -- read-only Mathlib PowerSeries substitution API retrieval.
#
# Reads:  <Mathlib>/Mathlib/RingTheory/PowerSeries/{Substitution,Basic,Inverse,Order,Evaluation,Expand}.lean
#         <Mathlib>/Mathlib/RingTheory/MvPowerSeries/Substitution.lean
# Writes: only inside this delivery directory (api-map.json, evidence/, .tmp/, logs/).
#
# No download, no lake update/build, no `lake env lean`, no edit of the main project,
# no change to Boundary files or the central fact-tree. Nothing here needs the network.
#
# Run from anywhere; the script locates itself.
#   powershell -ExecutionPolicy Bypass -File replay.ps1
#   pwsh -File replay.ps1
#   powershell -File replay.ps1 -MathlibRoot 'D:\path\to\mathlib'
#
# Mathlib root: if -MathlibRoot is omitted it is read from api-map.json's
# `mathlib.path` field, which is the path this delivery was actually built from.
# This file is deliberately pure ASCII so that Windows PowerShell 5.1 can parse it
# without a BOM (5.1 reads BOM-less .ps1 files in the ANSI code page, which would
# mangle any non-ASCII path literal).
#
# Expect: exit 0 and "REPLAY_OK". If Mathlib is absent or at a different commit the
# script fails loudly rather than silently reading a different version.
#
# evidence/ (durable, tracked) holds the extracted declarations, the signature dump,
# gapcheck.json, runs.json and spotcheck.json. .tmp/ is gitignored scratch space.

[CmdletBinding()]
param(
    [string]$MathlibRoot = '',
    [string]$ExpectedCommit = '85e3a25e006c35636f0e53b0e9296caca2685bc0'
)

$ErrorActionPreference = 'Stop'
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $here

$logDir = Join-Path $here 'logs'
$tmpDir = Join-Path $here '.tmp'
$evidDir = Join-Path $here 'evidence'
New-Item -ItemType Directory -Force -Path $logDir, $tmpDir, $evidDir | Out-Null

$env:TEMP = $tmpDir
$env:TMP = $tmpDir

function Assert-True([bool]$cond, [string]$msg) {
    if (-not $cond) { throw "ASSERT FAILED: $msg" }
    Write-Host "  ok: $msg"
}

# Assembled at runtime so that this file never contains the literal token it hunts for.
$needle = 'REPLACE' + '_WITH'

Write-Host '== 1. toolchain =='
$py = (Get-Command python -ErrorAction SilentlyContinue)
Assert-True ($null -ne $py) 'python is on PATH'
Write-Host ("  python: " + (& python --version 2>&1))

Write-Host '== 2. Mathlib pin =='
if (-not $MathlibRoot) {
    $mapPath = Join-Path $here 'api-map.json'
    Assert-True (Test-Path $mapPath) 'api-map.json present (its mathlib.path seeds the default root)'
    $MathlibRoot = (Get-Content -LiteralPath $mapPath -Raw -Encoding UTF8 | ConvertFrom-Json).mathlib.path
    Assert-True ([bool]$MathlibRoot) 'mathlib.path recovered from api-map.json'
}
Write-Host ("  root: " + $MathlibRoot)
Assert-True (Test-Path (Join-Path $MathlibRoot 'Mathlib')) "Mathlib root exists: $MathlibRoot"
$actual = (& git -C $MathlibRoot rev-parse HEAD 2>&1 | Out-String).Trim()
Write-Host ("  expected commit: " + $ExpectedCommit)
Write-Host ("  actual   commit: " + $actual)
Assert-True ($actual -eq $ExpectedCommit) 'Mathlib commit matches the baseline pin'

Write-Host '== 3. required source files exist =='
$required = @(
    'Mathlib/RingTheory/PowerSeries/Substitution.lean',
    'Mathlib/RingTheory/PowerSeries/Basic.lean',
    'Mathlib/RingTheory/PowerSeries/Inverse.lean',
    'Mathlib/RingTheory/PowerSeries/Order.lean',
    'Mathlib/RingTheory/PowerSeries/Evaluation.lean',
    'Mathlib/RingTheory/PowerSeries/Expand.lean',
    'Mathlib/RingTheory/MvPowerSeries/Substitution.lean'
)
foreach ($r in $required) {
    Assert-True (Test-Path (Join-Path $MathlibRoot ($r -replace '/', '\'))) $r
}

Write-Host '== 4. re-extract declarations verbatim =='
$sw = [System.Diagnostics.Stopwatch]::StartNew()
& python -B tools/extract.py tools/targets.json evidence/decls_dump.txt 2>&1 |
    Tee-Object -FilePath (Join-Path $logDir 'replay_extract.stdout.log')
Assert-True ($LASTEXITCODE -eq 0) 'extract.py exit 0'

& python -B tools/sigs.py evidence/decls_dump.txt evidence/sigs.txt 2>&1 |
    Tee-Object -FilePath (Join-Path $logDir 'replay_sigs.stdout.log')
Assert-True ($LASTEXITCODE -eq 0) 'sigs.py exit 0'

Write-Host '== 5. rebuild api-map.json =='
& python -B tools/build_api_map.py evidence/sigs.txt api-map.json 2>&1 |
    Tee-Object -FilePath (Join-Path $logDir 'replay_build_api_map.stdout.log')
Assert-True ($LASTEXITCODE -eq 0) 'build_api_map.py exit 0'
$sw.Stop()
Write-Host ("  rebuild seconds: " + [math]::Round($sw.Elapsed.TotalSeconds, 2))

Write-Host '== 6. verify the five gaps (negative searches) =='
& python -B tools/verify_gaps.py $MathlibRoot evidence/gapcheck.json 2>&1 |
    Tee-Object -FilePath (Join-Path $logDir 'replay_verify_gaps.stdout.log')
Assert-True ($LASTEXITCODE -eq 0) 'no gap contradicted'

Write-Host '== 7. api-map.json is well formed =='
$map = Get-Content -Raw -Encoding UTF8 api-map.json | ConvertFrom-Json
Assert-True ($map.schema_version -eq 1) 'schema_version == 1'
Assert-True ($map.task_id -eq 'T003') 'task_id == T003'
Assert-True ($map.status -eq 'RESEARCH_ONLY') 'status == RESEARCH_ONLY'
$n = $map.entries.Count
Write-Host ("  entries: " + $n)
Assert-True ($n -ge 100) 'at least 100 retrieved declarations'
Assert-True ($map.entries.Count -eq $map.totals.entries) 'totals.entries consistent'
Assert-True ($map.gaps.Count -eq 5) '5 documented gaps'
foreach ($e in $map.entries) {
    foreach ($f in 'name', 'file', 'signature', 'category') {
        if (-not $e.$f) { throw "ASSERT FAILED: entry missing $f : $($e.name)" }
    }
    if ($e.signature -match $needle) { throw "ASSERT FAILED: placeholder in $($e.name)" }
}

Write-Host '== 8. recorded file hashes still match =='
foreach ($row in $map.mathlib_files) {
    $p = Join-Path $MathlibRoot ($row.path -replace '/', '\')
    $h = (Get-FileHash -Algorithm SHA256 -LiteralPath $p).Hash.ToLower()
    if ($h -ne $row.sha256) {
        throw "ASSERT FAILED: hash drift in $($row.path) (recorded $($row.sha256), actual $h)"
    }
}
Write-Host ("  ok: " + $map.mathlib_files.Count + " Mathlib files match their recorded SHA256")

Write-Host '== 9. quoted declarations still live at the quoted file:line =='
$sub = Join-Path $MathlibRoot 'Mathlib\RingTheory\PowerSeries\Substitution.lean'
$subLines = Get-Content -LiteralPath $sub -Encoding UTF8
$quoted = @(
    @(40,  'abbrev HasSubst'),
    @(158, 'noncomputable def subst'),
    @(171, 'noncomputable def substAlgHom'),
    @(67,  'theorem HasSubst.of_constantCoeff_zero'),
    @(390, 'theorem subst_comp_subst_apply'),
    @(587, 'lemma subst_substInvOfIsUnit_right')
)
foreach ($q in $quoted) {
    $lineNo = [int]$q[0]
    $token = [string]$q[1]
    Assert-True ($subLines[$lineNo - 1] -like ('*' + $token + '*')) "$token at Substitution.lean:$lineNo"
}

Write-Host '== 10. no placeholder anywhere in the delivery =='
$scan = @('SUMMARY.md', 'replay.ps1', 'delivery.json',
          'tools/extract.py', 'tools/sigs.py', 'tools/build_api_map.py', 'tools/verify_gaps.py')
foreach ($name in $scan) {
    $p = Join-Path $here $name
    if (-not (Test-Path $p)) { throw "ASSERT FAILED: missing $name" }
    $text = Get-Content -LiteralPath $p -Raw -Encoding UTF8
    if ($text -match $needle) { throw "ASSERT FAILED: placeholder in $name" }
}
Assert-True $true 'no placeholder token in the delivery files'

Write-Host ''
Write-Host 'REPLAY_OK - retrieval reproduced; five gaps re-confirmed; six quoted declarations re-located; no build performed.'
Write-Host 'NOTE: this is a RESEARCH_ONLY artifact. It proves nothing about Lean compilation,'
Write-Host '      axioms, or editor admission, and it does not advance the mainline fact-tree.'
