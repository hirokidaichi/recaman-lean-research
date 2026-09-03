#!/bin/sh
# Post-processing of records.txt (columns: 1 kind 2 w 3 c 4 v 5 T 6 arcAtC
# 7 ex1 8 ex2 9 outcome 10 eventClock 11 "|" 12 n 13 step 14 q 15 r 16 arcN
# 17 arcStart 18 a(n-2) 19 a(n-1) 20 a(n+1) 21 a(n+2) 22 upperRun 23 lowerRun
# 24 sameArc 25 gap 26 n/c).  Usage: post.sh records.txt
R="$1"
echo "== (B) exceptions (upperRun=0 lowerRun=0): ladder classification =="
echo "   ladderSSS = subtraction at n, at n+1 (a(n+1) = w-(n+1)) and at n+2"
awk '$22==0 && $23==0 { n=$12; w=$2; down = ($13=="S" && $20==w-(n+1) && $21==$20-(n+2)); sp=($3<1000000000)?"discovery":"holdout"; key=sp" "$1" q="$14" ladderSSS="down; cnt[key]++ } END { for (k in cnt) print cnt[k], k }' "$R" | sort -k2,2 -k3,3 -k4,4
echo
echo "== (B) exceptions: step pattern at clocks n-1, n, n+1, n+2 (A/S from the values), per kind and split =="
echo "   SSSS/ASSS = ladder through w; AASS = spike (w is the peak); SSAA = valley (w is the bottom)"
awk '$22==0 && $23==0 { n=$12; w=$2; p = ($19>$18?"A":"S") $13 ($20>w?"A":"S") ($21>$20?"A":"S"); sp=($3<1000000000)?"discovery":"holdout"; key=sp" "$1" q="$14" pattern="p" sameArc="$24; cnt[key]++ } END { for (k in cnt) print cnt[k], k }' "$R" | sort -k2,2 -k3,3 -k4,4 -k5,5
echo
echo "== (B) exceptions: ladders (S at n, n+1, n+2) that end in a late landing at n+2 (a(n+2) < n+2) =="
awk '$22==0 && $23==0 { n=$12; w=$2; down = ($13=="S" && $20==w-(n+1) && $21==$20-(n+2)); late=($21 < n+2); key=$1" ladderSSS="down" lateAtN+2="late; cnt[key]++ } END { for (k in cnt) print cnt[k], k }' "$R" | sort -k2
echo
echo "== per kind: sameArc & q=L: run class (L=2 test/lockcand, 3 l3, 1 entry23/bandexit) =="
awk '{ L=($1=="test"||$1=="lockcand")?2:($1=="l3")?3:1; if ($24==1 && $14==L) { rc=($22?"upper":"")($23?"lower":""); if (rc=="") rc="neither"; if ($22&&$23) rc="both"; cnt[$1" "rc]++ } } END { for (k in cnt) print cnt[k], k }' "$R" | sort -k2
echo
echo "== per kind: earlierArc: (arcAtC-arcN, q) =="
awk '$24==0 { cnt[$1" dist="($6-$16)" q="$14]++ } END { for (k in cnt) print cnt[k], k }' "$R" | sort -k2,2 -k3,3 -k4,4
echo
echo "== test values, earlierArc: n/c min/max per q =="
awk '$1=="test" && $24==0 { q=$14; r=$26+0; if (!(q in mn) || r<mn[q]) mn[q]=r; if (!(q in mx) || r>mx[q]) mx[q]=r; c[q]++ } END { for (q in c) printf "q=%s count=%d n/c in [%.4f, %.4f]\n", q, c[q], mn[q], mx[q] }' "$R" | sort
echo
echo "== l3 values sameArc q=4 (C-prime exceptions): residue/n and run flags =="
awk '$1=="l3" && $24==1 && $14==4 { n=$12; printf "c=%s n=%s n/c=%s r/n=%.4f upper=%s lower=%s split=%s\n", $3, n, $26, $15/n, $22, $23, ($3<1000000000)?"discovery":"holdout" }' "$R"
