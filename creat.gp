set terminal post eps color enhanced font "Times,16" size 11cm,6cm
set out "creat.eps"

set logscale y 2
set key right bottom
set rmargin 0
set lmargin 0
#set size square

set multiplot 

set size 0.425,1
set origin 0.1,0
set ylabel "seconds" offset 5
set xlabel "height" offset -15,1.5
plot [3.1:11.9][0.016:5000] 'bench.dat' index 0 using 1:2 with line lt 1 lw 3 title "GF()",\
'bench.dat' index 1 using 1:2 with line lt 2 lw 3 title "sub<>",\
'bench.dat' index 2 using 1:($2+$3) with line lt 3 lw 3 title "Embed()",\
'bench.dat' index 3 using 1:2 with line lt 4 lw 3 title "T_2"
unset ylabel
unset xlabel

#

set size 0.425,1
set origin 0.55,0
set format y ""
plot [3.1:11.9][0.016:5000] 'bench.dat' index 4 using 1:2 with line lt 1 lw 3 title "GF()",\
'bench.dat' index 5 using 1:2 with line lt 2 lw 3 title "sub<>",\
'bench.dat' index 6 using 1:($2+$3) with line lt 3 lw 3 title "Embed()",\
'bench.dat' index 7 using 1:2 with line lt 4 lw 3 title "T_2",\
'bench.dat' index 8 using 1:2 with line lt 5 lw 3 title "Elliptic"
unset format

unset multiplot