$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..\..')).Path
$projectRoot = Join-Path $repoRoot 'candidates\core-kummer'
$buildRoot = Join-Path $projectRoot '.lake\build\lib\lean'
$logsRoot = Join-Path $PSScriptRoot 'build-import-logs'
$resultPath = Join-Path $PSScriptRoot 'build-import-results.json'
New-Item -ItemType Directory -Force -Path $logsRoot | Out-Null

$modules = @(
    @{ name = 'ContinuousKummerTheory.ContH1.Corestriction'; source = 'ContinuousKummerTheory\ContH1\Corestriction.lean'; output = 'ContinuousKummerTheory\ContH1\Corestriction.olean' },
    @{ name = 'ContinuousKummerTheory.Kummer.Restriction'; source = 'ContinuousKummerTheory\Kummer\Restriction.lean'; output = 'ContinuousKummerTheory\Kummer\Restriction.olean' },
    @{ name = 'ContinuousKummerTheory.Kummer.Corestriction'; source = 'ContinuousKummerTheory\Kummer\Corestriction.lean'; output = 'ContinuousKummerTheory\Kummer\Corestriction.olean' },
    @{ name = 'ContinuousKummerTheory.Kummer.Values'; source = 'ContinuousKummerTheory\Kummer\Values.lean'; output = 'ContinuousKummerTheory\Kummer\Values.olean' },
    @{ name = 'ContinuousKummerTheory.Kummer.Specialization'; source = 'ContinuousKummerTheory\Kummer\Specialization.lean'; output = 'ContinuousKummerTheory\Kummer\Specialization.olean' },
    @{ name = 'ContinuousKummerTheory.Kummer.Decomposition'; source = 'ContinuousKummerTheory\Kummer\Decomposition.lean'; output = 'ContinuousKummerTheory\Kummer\Decomposition.olean' },
    @{ name = 'ContinuousKummerTheory.Kummer.DecompositionSurjective'; source = 'ContinuousKummerTheory\Kummer\DecompositionSurjective.lean'; output = 'ContinuousKummerTheory\Kummer\DecompositionSurjective.olean' }
)
$results = @()
$pushed = $false
foreach ($module in $modules) {
    $results += [ordered]@{
        module = $module.name
        source = $module.source
        output = (Join-Path $buildRoot $module.output)
        log = (Join-Path $logsRoot ($module.name + '.log'))
        status = 'pending'
        exitCode = $null
    }
}
$overallExitCode = 0
$startedAt = [DateTime]::UtcNow.ToString('o')
$utf8NoBom = New-Object System.Text.UTF8Encoding($false)

try {
    Push-Location $projectRoot
    $pushed = $true
    for ($i = 0; $i -lt $modules.Count; $i++) {
        $module = $modules[$i]
        $entry = $results[$i]
        $outputPath = $entry.output
        $outputDirectory = Split-Path -Parent $outputPath
        New-Item -ItemType Directory -Force -Path $outputDirectory | Out-Null
        $logPath = $entry.log
        try {
            $messages = & lake env lean -DwarningAsError=true -o $outputPath $module.source 2>&1
            $code = $LASTEXITCODE
            $messages | Out-File -LiteralPath $logPath -Encoding utf8
            if ($null -eq $code) { $code = 0 }
        }
        catch {
            $_ | Out-String | Out-File -LiteralPath $logPath -Encoding utf8
            $code = $LASTEXITCODE
            if ($null -eq $code -or $code -eq 0) { $code = 1 }
        }
        $entry.exitCode = [int]$code
        if ($code -eq 0) {
            $entry.status = 'passed'
        }
        else {
            $entry.status = 'failed'
            $overallExitCode = [int]$code
            for ($j = $i + 1; $j -lt $results.Count; $j++) {
                $results[$j].status = 'not_run_after_failure'
            }
            break
        }
    }
}
catch {
    if ($overallExitCode -eq 0) { $overallExitCode = 1 }
    $fatalLog = Join-Path $logsRoot 'runner-error.log'
    $_ | Out-String | Out-File -LiteralPath $fatalLog -Encoding utf8
}
finally {
    if ($pushed) { Pop-Location }
    $report = [ordered]@{
        project = 'candidates/core-kummer'
        sourceSelection = 'Six modules are from pin 98b67dfe9c82415aa17caa633d93960b6829af2e; DecompositionSurjective is from continuous-kummer-theory HEAD 1d5194fcc63ddeb7a8cdb6c98d59452503db60fa.'
        command = 'lake env lean -DwarningAsError=true -o <module.olean> <module.lean>'
        startedAtUtc = $startedAt
        finishedAtUtc = [DateTime]::UtcNow.ToString('o')
        exitCode = [int]$overallExitCode
        modules = $results
    }
    $json = $report | ConvertTo-Json -Depth 6
    [System.IO.File]::WriteAllText($resultPath, $json, $utf8NoBom)
}
exit $overallExitCode