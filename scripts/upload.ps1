#
# upload the given file to the snp server
# 

param(
    [Parameter(Mandatory=$true)]
    [String]$source,
    [Parameter(Mandatory=$true)]
    [String]$todir
)

$destination = "\\ziqiao-titan2\E`$\zz-test\$todir"
$WSL_DIR = "\\wsl$\Ubuntu\"
$filepath = "$WSL_DIR\$source"
Write-Output "upload file $filepath to $destination"
Copy-Item $filepath $destination