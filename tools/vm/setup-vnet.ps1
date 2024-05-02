New-VMSwitch -SwitchName "SNPBridge" -SwitchType Internal
$snpbridge = Get-NetAdapter -name "vEthernet (SNPBridge)"
New-NetIPAddress -IPAddress 192.168.0.1 -PrefixLength 24 -InterfaceIndex $snpbridge.ifIndex
New-NetNat -Name SNPNAT -InternalIPInterfaceAddressPrefix 192.168.0.0/24