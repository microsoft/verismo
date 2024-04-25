for i in `seq 1 100`;
do
echo "2 1 test" > /proc/verismo
dmesg |tail -n 11|grep "req.op" | cut -d" " -f7,11  >> result3.txt

echo "1 1 test" > /proc/verismo
dmesg |tail -n 11|grep "req.op" | cut -d" " -f7,11  >> result3.txt

done
for i in `seq 1 100`;
do
for code in 4 6 8
do
bytes32=$(xxd -l 32 -c 32 -p < /dev/random)
echo "${code} 0 ${bytes32}" > /proc/verismo
dmesg |tail -n 11|grep "req.op" | cut -d" " -f7,11  >> result3.txt

done
done
for i in `seq 1 20`;
do
echo "5 0 0" > /proc/verismo
dmesg |tail -n 11|grep "req.op" | cut -d" " -f7,11  >> result3.txt
done

dmesg |grep "req.op" | cut -d" " -f7,11  >> result.txt
