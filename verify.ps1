$ErrorActionPreference = 'Stop'
$opfOriginalLocation = Get-Location
try {
  Set-Location -LiteralPath $PSScriptRoot
  New-Item -ItemType Directory -Path 'verification' -Force | Out-Null
  $opfLibraryFiles = @('OpenProblemFormalizations.lean') +
    @(Get-ChildItem -LiteralPath 'OpenProblemFormalizations' -Filter '*.lean' -Recurse |
      ForEach-Object { $_.FullName.Substring($PSScriptRoot.Length + 1).Replace('\','/') })
  $opfFiles = $opfLibraryFiles + @('Check.lean','Audit.lean')
  $opfForbidden = '\b(sorry|admit|sorryAx|native_decide|unsafe)\b|(?m)^\s*(axiom|constant)\s'
  foreach ($opfFile in $opfFiles) {
    $opfText = Get-Content -LiteralPath $opfFile -Raw -Encoding utf8
    if ($opfText -match $opfForbidden) { throw "Forbidden construct in $opfFile" }
    if ($opfText -match '(?m)[ \t]+$|^(<<<<<<<|=======|>>>>>>>)') {
      throw "Whitespace or merge marker in $opfFile"
    }
  }
  $opfInitialHashes = @{}
  foreach ($opfFile in $opfFiles) {
    $opfInitialHashes[$opfFile] = (Get-FileHash -LiteralPath $opfFile -Algorithm SHA256).Hash
  }
  $opfModules = @{}
  foreach ($opfFile in $opfLibraryFiles) {
    $opfModules[$opfFile.Replace('/','.').Replace('.lean','')] = $opfFile
  }
  $opfQueue = [Collections.Generic.Queue[string]]::new()
  $opfSeen = [Collections.Generic.HashSet[string]]::new()
  $opfQueue.Enqueue('OpenProblemFormalizations')
  while ($opfQueue.Count -gt 0) {
    $opfModule = $opfQueue.Dequeue()
    if (-not $opfSeen.Add($opfModule)) { continue }
    $opfText = Get-Content -LiteralPath $opfModules[$opfModule] -Raw
    foreach ($opfMatch in [regex]::Matches($opfText, '(?m)^import\s+([A-Za-z0-9_.]+)\s*$')) {
      $opfImport = $opfMatch.Groups[1].Value
      if ($opfModules.ContainsKey($opfImport)) { $opfQueue.Enqueue($opfImport) }
    }
  }
  foreach ($opfModule in $opfModules.Keys) {
    if (-not $opfSeen.Contains($opfModule)) { throw "Unaudited module: $opfModule" }
  }
  & lake build 2>&1 | Tee-Object -FilePath 'verification/build.log'
  if ($LASTEXITCODE -ne 0) { throw 'Library build failed' }
  & lake env lean Check.lean 2>&1 | Tee-Object -FilePath 'verification/check.log'
  if ($LASTEXITCODE -ne 0) { throw 'Statement checks failed' }
  & lake env lean Audit.lean 2>&1 | Tee-Object -FilePath 'verification/audit.log'
  if ($LASTEXITCODE -ne 0) { throw 'Axiom audit failed' }
  $opfAudit = Get-Content -LiteralPath 'verification/audit.log' -Raw
  if ($opfAudit -notmatch 'Kernel audit passed: (\d+) declarations, (\d+) theorem constants') {
    throw 'Missing successful audit summary'
  }
  $opfDeclarations = [int]$Matches[1]
  $opfTheorems = [int]$Matches[2]
  foreach ($opfFile in $opfFiles) {
    if ((Get-FileHash -LiteralPath $opfFile -Algorithm SHA256).Hash -ne $opfInitialHashes[$opfFile]) {
      throw "Source changed during verification; rerun: $opfFile"
    }
  }
  $opfFinalLibraryCount = 1 + @(Get-ChildItem -LiteralPath 'OpenProblemFormalizations' -Filter '*.lean' -Recurse).Count
  if ($opfFinalLibraryCount -ne $opfLibraryFiles.Count) { throw 'Module set changed during verification' }
  $opfManifest = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
  $opfReport = [ordered]@{
    checked_at_utc = [DateTime]::UtcNow.ToString('o')
    lean_toolchain = (Get-Content -LiteralPath 'lean-toolchain' -Raw).Trim()
    mathlib_revision = ($opfManifest.packages | Where-Object name -eq 'mathlib').rev
    build = 'passed'
    statement_checks = 'passed'
    axiom_audit = 'passed'
    declarations = $opfDeclarations
    theorem_constants = $opfTheorems
    library_modules = $opfLibraryFiles.Count
    permitted_axioms = @('propext','Classical.choice','Quot.sound')
    forbidden_construct_scan = 'passed'
    whitespace_scan = 'passed'
    module_coverage = 'passed'
    source_hashes = @($opfFiles | Sort-Object | ForEach-Object {
      @{path=$_; sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant()}
    })
  }
  $opfReport | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath 'verification/manifest.json' -Encoding utf8
  Write-Output "Verified $opfDeclarations declarations, $opfTheorems theorem constants."
} finally {
  Set-Location -LiteralPath $opfOriginalLocation
}
