#!/bin/bash
mkdir input
for i in {1..50}
do
    let size=i*10
    let op=10*i*3
    python3 generate_instance.py 10000 $size $op > input_100/$size.in
    echo $i
done
