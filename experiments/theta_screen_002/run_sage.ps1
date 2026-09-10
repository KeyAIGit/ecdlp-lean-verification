$ErrorActionPreference = "Stop"

$Image = "sagemath/sagemath:10.9"
$RepoRoot = Resolve-Path (Join-Path $PSScriptRoot "../..")
$Results = Join-Path $PSScriptRoot "sage_results"
$ResultZip = Join-Path $PSScriptRoot "sage_results.zip"

New-Item -ItemType Directory -Force -Path $Results | Out-Null
Remove-Item -Force -ErrorAction SilentlyContinue $ResultZip

Write-Host "Pulling official SageMath image $Image"
docker pull $Image

Write-Host "Running exact secp256k1 cubic-descent verification"
docker run --rm `
  -v "${RepoRoot}:/work" `
  -w /work `
  $Image `
  sage -python experiments/theta_screen_002/verify_secp.py

$configurations = @(
  @{ h = 1; system = "direct";     order = "lex";        layout = "coordinate" },
  @{ h = 1; system = "direct";     order = "degrevlex"; layout = "coordinate" },
  @{ h = 1; system = "projective"; order = "degrevlex"; layout = "coordinate" },
  @{ h = 1; system = "projective"; order = "degrevlex"; layout = "intermediate_first" },
  @{ h = 2; system = "direct";     order = "lex";        layout = "coordinate" },
  @{ h = 2; system = "direct";     order = "degrevlex"; layout = "coordinate" },
  @{ h = 2; system = "projective"; order = "degrevlex"; layout = "coordinate" },
  @{ h = 2; system = "projective"; order = "degrevlex"; layout = "intermediate_first" },
  @{ h = 3; system = "direct";     order = "lex";        layout = "coordinate" },
  @{ h = 3; system = "projective"; order = "degrevlex"; layout = "intermediate_first" },
  @{ h = 4; system = "direct";     order = "lex";        layout = "coordinate" },
  @{ h = 4; system = "projective"; order = "degrevlex"; layout = "intermediate_first" }
)

foreach ($cfg in $configurations) {
  $layoutSuffix = if ($cfg.system -eq "projective") { "_$($cfg.layout)" } else { "" }
  $name = "h$($cfg.h)_$($cfg.system)_$($cfg.order)$layoutSuffix.json"
  $containerOut = "/work/experiments/theta_screen_002/sage_results/$name"

  Write-Host ""
  Write-Host "Running h=$($cfg.h), system=$($cfg.system), order=$($cfg.order), layout=$($cfg.layout)"

  docker run --rm `
    -v "${RepoRoot}:/work" `
    -w /work `
    $Image `
    sage -python experiments/theta_screen_002/singular_factorbase.py `
      --h $cfg.h `
      --system $cfg.system `
      --order $cfg.order `
      --layout $cfg.layout `
      --timeout 180 `
      --out $containerOut
}

Compress-Archive -Path "$Results\*" -DestinationPath $ResultZip -Force

Write-Host ""
Write-Host "Send back this file: $ResultZip"
Get-ChildItem $Results
