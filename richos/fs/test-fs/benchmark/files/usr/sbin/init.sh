mkdir -p /dev/pts
mount devpts /dev/pts -t devpts
mkdir -p /securityfs
mount -t securityfs securityfs /securityfs
mount -t sysfs sysfs /sys
#/usr/bin/tpm2_pcrread sha1:10
#echo "Computed measurement using runtime measure traces:"
#/root/ima-tests/ima_measure /securityfs/ima/binary_runtime_measurements
#echo "VMPL0-vTPM provided PCR value"
#/usr/bin/tpm2_pcrread sha1:10
#mknod /dev/kvm c 10 232
#chmod a+rw /dev/kvm
/sbin/ip link set dev eth0 up
ifup eth1
echo "config addr"
/sbin/ip address add 192.168.0.106/24 dev eth0
echo "config route"
/sbin/ip route add default via 192.168.0.1 dev eth0
echo "set up lo"
/sbin/ip link set dev lo up
echo "config addr for lo"
/sbin/ip address add 127.0.0.1/8 dev lo
echo "sshd started"
/usr/bin/ssh-keygen -A
/usr/sbin/sshd
echo "show addr"
ip addr
echo "show route"
ip route show
hostname vmpl2
#/bin/sh /root/tpm_quote.sh
