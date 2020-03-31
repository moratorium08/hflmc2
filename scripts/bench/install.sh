#!/bin/sh

KHFLMC2=/home/katsura/hflmc2/
HHFLMC2=/home/katsura/github.com/hogeyama/hflmc2
HFLMC=/home/katsura/misc/hflmc
BURN=/home/katsura/github.com/penteract/HigherOrderHornRefinement/

BASE=/home/katsura/hflmc2/scripts/bench/benchmark

cp $BASE/kat_hflmc2.py $KHFLMC2/benchmark/bench.py
cp $BASE/iwa_hflmc2.py $HHFLMC2/benchmark/bench.py
cp $BASE/hflmc.py $HFLMC/benchmark/bench.py
cp $BASE/burn.py  $BURN/bench.py