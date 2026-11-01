# Independent low-inversion pruning (H04)
Candidate: any positive M,m,L,s and arbitrary h,K, I=M(m+s)+Ls<=14 -> third ray local count<=2.
Falsifier: direct finite1284 cases h0..5/clocks0..5; fresh h17/clocks0..18 and independent reverse evaluation214 cases. Both max2, only COMPUTED.
Proof plan (no table):
1. initial S q gives Q=q+m+s>=3, Q²2I1<=29 -> Q3or5 -> I4or12, unique clock.
2. first A e gives b=m+s>=2 and 2eb+2Ls=b²-1. Since e<=M, b²<=2I+1<=29. b2..5, even impossible. b3 -> onlyclock2. b5 -> e1 or2; e1 Ls7 conflicts i>=0/L<=5/s<=4; e2 Ls2 -> clock2 or (M,m,L,s)=(2,3,1,2), clock3.
3. second S q<=m gives Q=q+s>=2, Q²2Ls1<=25 -> Q3or5. Q5 -> Ls12 and Mb<=2 =>m=s=M1 contradictq4<=m. Q3 -> Ls4 -> i2 or L4/s1/m>=2/i0.
4. firstA exception implies b5, so initial S q+b>=6 impossible and second S0 impossible L1vs4. Local subset2/3.
5. if L4/s1/m>=2, initial S has I12 and M(m+1)=8; q+m+1=5 =>m2or3, onlym3/M2. Its clock0. Local subset0/2.
6. otherwise firstA andsecondS only2, initial S oneclock. Count union<=2.
Old E415 refutes unconditional local<=2/3; this measurable I cap is essential input supplied later by the same actual counter. No independent tags; arbitrary h and K, no finite source/history bound assumption.
