function setVtlByDev{
        param(
                [string[]]$VMNAME,
                [int] $Vtl,
                [Microsoft.HyperV.PowerShell.VMDevice] $vmdev)
        $VM = Get-VM -name $VMNAME
        if ($VM -eq $null) {
                 Write-Host "The VM doesn't exist!"
        }else {
                $id = $VM.id
                $config = $VM.ConfigurationLocation
                $devid= $vmdev.id.Split("\")[1].ToLower()
                $Cmd = ".\HvsEdit.exe `"$config\Virtual Machines\$id.vmcx`" -set int `"/configuration/`_$devid`_/TargetVtl`" $Vtl"
                Write-Host $Cmd
                Invoke-Expression $Cmd
        }
}

# $vmname="linux-snp-direct-tpm"
$vmname=$args[0]
$linux0=(Resolve-Path $args[1]).Path
$vhd0=$args[2]
$vhd2=$args[3]
$rundir="e:/zz-test/vm/"
$fsrc0=$vhd0
$fsrc2=$vhd2
$fdst0="$rundir/rootfs-$vmname-0.vhdx"
$fdst2="$rundir/rootfs-$vmname-2.vhdx"
$NextVtl=0


# Remove old VM
remove-vm $vmname

# linux2 is located in fdst0

New-HclVM -name "$vmname" -isolation Snp -MemoryStartupBytes 8196MB
set-VMprocessor -VMName $vmname -Count 8
Add-VMScsiController -VMName $vmname
Set-VMFirmware -VMName $vmname -EnableSecureBoot Off

# a small SNP enlightened linux boot
Set-VMFirmwareFile -Name $vmname -Path $linux0

#Assign NIC to VMPL0 (VTL2)
Add-VMNetworkAdapter -VMName $vmname -SwitchName SNPBridge  -name "net0"
$nic0=(Get-VMNetworkAdapter -Name net0 -VMName $vmname)
setVtlByDev -VMNAME $vmname -Vtl 2 -vmdev $nic0

Add-VMNetworkAdapter -VMName $vmname -SwitchName SNPBridge -name "net3"
$nic3=(Get-VMNetworkAdapter -Name net3 -VMName $vmname)
setVtlByDev -VMNAME $vmname -Vtl 2 -vmdev $nic3

#Assign NIC to VMPL2 (VTL0)
Add-VMNetworkAdapter -VMName $vmname -SwitchName SNPBridge -name "net1"
$nic1=(Get-VMNetworkAdapter -Name net1 -VMName $vmname)
setVtlByDev -VMNAME $vmname -Vtl $NextVtl -vmdev $nic1

Add-VMNetworkAdapter -VMName $vmname -SwitchName SNPBridge -name "net2"
$nic2=(Get-VMNetworkAdapter -Name net2 -VMName $vmname)
setVtlByDev -VMNAME $vmname -Vtl $NextVtl -vmdev $nic2


if ($fsrc0 -eq "none") {
	Write-Host "No vmpl0 disk"
} else {
	rm $fdst0
	cp $fsrc0 $fdst0
	Add-VMHardDiskDrive -VMName $vmname -Path $fdst0 -ControllerType SCSI -ControllerNumber 1 -ControllerLocation 0
	#Assign Scsi to VMPL0(VTL2)
	$scsi0=(Get-VMScsiController -VMName $vmname -ControllerNumber 1)
	setVtlByDev -VMNAME $vmname -Vtl 2 -vmdev $scsi0
}
if ($fsrc2 -eq "none") {
	Write-Host "No vmpl2 disk"
} else {
	rm $fdst2
	cp $fsrc2 $fdst2
	Add-VMHardDiskDrive -VMName $vmname -Path $fdst2 -ControllerType SCSI -ControllerNumber 0 -ControllerLocation 0
	#Assign Scsi to VMPL2(VTL0)
	$scsi2=(Get-VMScsiController -VMName $vmname -ControllerNumber 0)
	setVtlByDev -VMNAME $vmname -Vtl $NextVtl -vmdev $scsi2
}

$VM = Get-VM -name $vmname
$id=$VM.id
$config = $VM.ConfigurationLocation
.\HvsEdit.exe `"$config\Virtual Machines\$id.vmcx`" -set bool /configuration/settings/isolation/vtl_restricted_interrupt true
#Start-VM $vmname
#Set-VMComPort -VMName "ivm" -Number 2 -Path \\.\pipe\dbg1
#$comport=(Get-VMComPort -VMName $vmname -Number 2)
#setVtlByDev -VMNAME $vmname -Vtl 2 -vmdev $comport