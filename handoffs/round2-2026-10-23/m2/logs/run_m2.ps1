param([string]$Root)
$ErrorActionPreference = 'Continue'
if (-not $Root) { throw 'Root parameter required' }
$env:TEMP = Join-Path $Root '.tmp'
$env:TMP  = $env:TEMP
$cand = Join-Path $Root 'candidates\orbit-quotient'
$logDir = Join-Path $env:TEMP 'logs'
New-Item -ItemType Directory -Force -Path $logDir | Out-Null
New-Item -ItemType Directory -Force -Path (Join-Path $cand '.lake\build\lib\lean\Candidates') | Out-Null
$toolDir = Join-Path $cand 'tool'

$results = New-Object System.Collections.ArrayList

function Run-Step {
    param([string]$Id, [string]$WorkDir, [string]$CmdLine)
    $outFile = Join-Path $logDir "$Id.stdout.txt"
    $errFile = Join-Path $logDir "$Id.stderr.txt"
    $full = "$CmdLine 1> `"$outFile`" 2> `"$errFile`""
    $sw = [Diagnostics.Stopwatch]::StartNew()
    Push-Location -LiteralPath $WorkDir
    cmd /c $full
    $code = $LASTEXITCODE
    Pop-Location
    $sw.Stop()
    $outBytes = 0; if (Test-Path -LiteralPath $outFile) { $outBytes = (Get-Item -LiteralPath $outFile).Length }
    $errBytes = 0; if (Test-Path -LiteralPath $errFile) { $errBytes = (Get-Item -LiteralPath $errFile).Length }
    $rec = [ordered]@{
        id = $Id
        argv = @('cmd','/c',$CmdLine)
        cwd = $WorkDir
        exit_code = $code
        elapsed_seconds = [math]::Round($sw.Elapsed.TotalSeconds, 3)
        stdout = "$Id.stdout.txt"
        stderr = "$Id.stderr.txt"
        stdout_bytes = $outBytes
        stderr_bytes = $errBytes
    }
    [void]$results.Add([pscustomobject]$rec)
    Write-Output ("[{0}] exit={1} {2}s out={3}B err={4}B" -f $Id, $code, $rec.elapsed_seconds, $outBytes, $errBytes)
}

Run-Step -Id 'git-head' -WorkDir $Root -CmdLine 'git rev-parse HEAD'
Run-Step -Id 'lean-version' -WorkDir $cand -CmdLine 'lake env lean --version'
Run-Step -Id 'python-version' -WorkDir $cand -CmdLine 'python --version'
Run-Step -Id 'tool-unittest' -WorkDir $toolDir -CmdLine 'python -B test_hull_tool.py -v'
Run-Step -Id 'tool-example-two-three-four' -WorkDir $toolDir -CmdLine 'python -B hull_tool.py --input examples/two-three-four.json --out runs/two-three-four-fixed'
Run-Step -Id 'lean-entry' -WorkDir $cand -CmdLine 'lake env lean --json -DwarningAsError=true -o .lake/build/lib/lean/Candidates/OrbitQuotient.olean -i .lake/build/lib/lean/Candidates/OrbitQuotient.ilean Candidates/OrbitQuotient.lean'
Run-Step -Id 'lean-axioms' -WorkDir $cand -CmdLine 'lake env lean --json -DwarningAsError=true Candidates/Axioms.lean'
Run-Step -Id 'lean-hulltool' -WorkDir $cand -CmdLine 'lake env lean --json -DwarningAsError=true -o .lake/build/lib/lean/Candidates/HullTool.olean -i .lake/build/lib/lean/Candidates/HullTool.ilean Candidates/HullTool.lean'
Run-Step -Id 'lean-tool-certificate' -WorkDir $cand -CmdLine 'lake env lean --json -DwarningAsError=true tool/runs/two-three-four-fixed/certificate.lean'

$json = $results | ConvertTo-Json -Depth 5
[IO.File]::WriteAllText((Join-Path $logDir 'results.json'), $json, (New-Object System.Text.UTF8Encoding($false)))
Write-Output '--- done ---'
