echo "Extend PCR"
pcrdata=$(xxd -l 32 -c 32 -p < /dev/random)
echo "4 0 ${pcrdata}" > /proc/verismo
dmesg |tail -n 11|grep "req"

echo "Attest PCR"
bytes32=$(xxd -l 32 -c 32 -p < /dev/random)
echo "6 0 ${bytes32}" > /proc/verismo
dmesg |tail -n 11|grep "req"
cat /proc/verismo > report
/verismo/decode_report ./report
echo "Make page shared"
echo "2 1 test" > /proc/verismo
dmesg |tail -n 11|grep "req"
echo "Make page private"
echo "1 1 test" > /proc/verismo
dmesg |tail -n 11|grep "req"

echo "Lock kernel codes"
echo "5 0 0" > /proc/verismo
dmesg |tail -n 11|grep "req"
