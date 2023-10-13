3-bit ripple carry adder:

  $ adder | grep -v "CPU time"
  
  
  ripple 1
  <<(S_0 <=> ~(X_0 <=> Y_0)) /\ (CIN_1 <=> X_0 /\ Y_0)>>
  number of variables: 4
  
  
  ripple 2
  <<((S_0 <=> ~(X_0 <=> Y_0)) /\ (CIN_1 <=> X_0 /\ Y_0)) /\ (S_1 <=> ~(~(X_1 <=> Y_1) <=> CIN_1)) /\ (CIN_2 <=> X_1 /\ Y_1 \/ (X_1 \/ Y_1) /\ CIN_1)>>
  number of variables: 8
  
  
  ripple 3
  <<((S_0 <=> ~(X_0 <=> Y_0)) /\ (CIN_1 <=> X_0 /\ Y_0)) /\ ((S_1 <=> ~(~(X_1 <=> Y_1) <=> CIN_1)) /\ (CIN_2 <=> X_1 /\ Y_1 \/ (X_1 \/ Y_1) /\ CIN_1)) /\ (S_2 <=> ~(~(X_2 <=> Y_2) <=> CIN_2)) /\ (CIN_3 <=> X_2 /\ Y_2 \/ (X_2 \/ Y_2) /\ CIN_2)>>
  number of variables: 12
  
  
  ripple 3 DNF foo:
  <<CIN_1 /\ CIN_2 /\ CIN_3 /\ S_1 /\ S_2 /\ X_0 /\ X_1 /\ X_2 /\ Y_0 /\ Y_1 /\ Y_2 /\ ~S_0 \/ CIN_1 /\ CIN_2 /\ CIN_3 /\ S_1 /\ X_0 /\ X_1 /\ X_2 /\ Y_0 /\ Y_1 /\ ~S_0 /\ ~S_2 /\ ~Y_2 \/ CIN_1 /\ CIN_2 /\ CIN_3 /\ S_1 /\ X_0 /\ X_1 /\ Y_0 /\ Y_1 /\ Y_2 /\ ~S_0 /\ ~S_2 /\ ~X_2 \/ CIN_1 /\ CIN_2 /\ CIN_3 /\ S_2 /\ X_0 /\ X_1 /\ X_2 /\ Y_0 /\ Y_2 /\ ~S_0 /\ ~S_1 /\ ~Y_1 \/ CIN_1 /\ CIN_2 /\ CIN_3 /\ S_2 /\ X_0 /\ X_2 /\ Y_0 /\ Y_1 /\ Y_2 /\ ~S_0 /\ ~S_1 /\ ~X_1 \/ CIN_1 /\ CIN_2 /\ CIN_3 /\ X_0 /\ X_1 /\ X_2 /\ Y_0 /\ ~S_0 /\ ~S_1 /\ ~S_2 /\ ~Y_1 /\ ~Y_2 \/ CIN_1 /\ CIN_2 /\ CIN_3 /\ X_0 /\ X_1 /\ Y_0 /\ Y_2 /\ ~S_0 /\ ~S_1 /\ ~S_2 /\ ~X_2 /\ ~Y_1 \/ CIN_1 /\ CIN_2 /\ CIN_3 /\ X_0 /\ X_2 /\ Y_0 /\ Y_1 /\ ~S_0 /\ ~S_1 /\ ~S_2 /\ ~X_1 /\ ~Y_2 \/ CIN_1 /\ CIN_2 /\ CIN_3 /\ X_0 /\ Y_0 /\ Y_1 /\ Y_2 /\ ~S_0 /\ ~S_1 /\ ~S_2 /\ ~X_1 /\ ~X_2 \/ CIN_1 /\ CIN_2 /\ S_1 /\ S_2 /\ X_0 /\ X_1 /\ Y_0 /\ Y_1 /\ ~CIN_3 /\ ~S_0 /\ ~X_2 /\ ~Y_2 \/ CIN_1 /\ CIN_2 /\ S_2 /\ X_0 /\ X_1 /\ Y_0 /\ ~CIN_3 /\ ~S_0 /\ ~S_1 /\ ~X_2 /\ ~Y_1 /\ ~Y_2 \/ CIN_1 /\ CIN_2 /\ S_2 /\ X_0 /\ Y_0 /\ Y_1 /\ ~CIN_3 /\ ~S_0 /\ ~S_1 /\ ~X_1 /\ ~X_2 /\ ~Y_2 \/ CIN_1 /\ CIN_3 /\ S_1 /\ X_0 /\ X_2 /\ Y_0 /\ Y_2 /\ ~CIN_2 /\ ~S_0 /\ ~S_2 /\ ~X_1 /\ ~Y_1 \/ CIN_1 /\ S_1 /\ S_2 /\ X_0 /\ X_2 /\ Y_0 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~X_1 /\ ~Y_1 /\ ~Y_2 \/ CIN_1 /\ S_1 /\ S_2 /\ X_0 /\ Y_0 /\ Y_2 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~X_1 /\ ~X_2 /\ ~Y_1 \/ CIN_1 /\ S_1 /\ X_0 /\ Y_0 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~S_2 /\ ~X_1 /\ ~X_2 /\ ~Y_1 /\ ~Y_2 \/ CIN_2 /\ CIN_3 /\ S_0 /\ S_2 /\ X_0 /\ X_1 /\ X_2 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~S_1 /\ ~Y_0 \/ CIN_2 /\ CIN_3 /\ S_0 /\ S_2 /\ X_1 /\ X_2 /\ Y_0 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~S_1 /\ ~X_0 \/ CIN_2 /\ CIN_3 /\ S_0 /\ X_0 /\ X_1 /\ X_2 /\ Y_1 /\ ~CIN_1 /\ ~S_1 /\ ~S_2 /\ ~Y_0 /\ ~Y_2 \/ CIN_2 /\ CIN_3 /\ S_0 /\ X_0 /\ X_1 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~S_1 /\ ~S_2 /\ ~X_2 /\ ~Y_0 \/ CIN_2 /\ CIN_3 /\ S_0 /\ X_1 /\ X_2 /\ Y_0 /\ Y_1 /\ ~CIN_1 /\ ~S_1 /\ ~S_2 /\ ~X_0 /\ ~Y_2 \/ CIN_2 /\ CIN_3 /\ S_0 /\ X_1 /\ Y_0 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~S_1 /\ ~S_2 /\ ~X_0 /\ ~X_2 \/ CIN_2 /\ CIN_3 /\ S_2 /\ X_1 /\ X_2 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~S_0 /\ ~S_1 /\ ~X_0 /\ ~Y_0 \/ CIN_2 /\ CIN_3 /\ X_1 /\ X_2 /\ Y_1 /\ ~CIN_1 /\ ~S_0 /\ ~S_1 /\ ~S_2 /\ ~X_0 /\ ~Y_0 /\ ~Y_2 \/ CIN_2 /\ CIN_3 /\ X_1 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~S_0 /\ ~S_1 /\ ~S_2 /\ ~X_0 /\ ~X_2 /\ ~Y_0 \/ CIN_2 /\ S_0 /\ S_2 /\ X_0 /\ X_1 /\ Y_1 /\ ~CIN_1 /\ ~CIN_3 /\ ~S_1 /\ ~X_2 /\ ~Y_0 /\ ~Y_2 \/ CIN_2 /\ S_0 /\ S_2 /\ X_1 /\ Y_0 /\ Y_1 /\ ~CIN_1 /\ ~CIN_3 /\ ~S_1 /\ ~X_0 /\ ~X_2 /\ ~Y_2 \/ CIN_2 /\ S_2 /\ X_1 /\ Y_1 /\ ~CIN_1 /\ ~CIN_3 /\ ~S_0 /\ ~S_1 /\ ~X_0 /\ ~X_2 /\ ~Y_0 /\ ~Y_2 \/ CIN_3 /\ S_0 /\ S_1 /\ X_0 /\ X_1 /\ X_2 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~S_2 /\ ~Y_0 /\ ~Y_1 \/ CIN_3 /\ S_0 /\ S_1 /\ X_0 /\ X_2 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~S_2 /\ ~X_1 /\ ~Y_0 \/ CIN_3 /\ S_0 /\ S_1 /\ X_1 /\ X_2 /\ Y_0 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~S_2 /\ ~X_0 /\ ~Y_1 \/ CIN_3 /\ S_0 /\ S_1 /\ X_2 /\ Y_0 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~S_2 /\ ~X_0 /\ ~X_1 \/ CIN_3 /\ S_0 /\ X_0 /\ X_2 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~S_1 /\ ~S_2 /\ ~X_1 /\ ~Y_0 /\ ~Y_1 \/ CIN_3 /\ S_0 /\ X_2 /\ Y_0 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~S_1 /\ ~S_2 /\ ~X_0 /\ ~X_1 /\ ~Y_1 \/ CIN_3 /\ S_1 /\ X_1 /\ X_2 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~S_0 /\ ~S_2 /\ ~X_0 /\ ~Y_0 /\ ~Y_1 \/ CIN_3 /\ S_1 /\ X_2 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~S_0 /\ ~S_2 /\ ~X_0 /\ ~X_1 /\ ~Y_0 \/ CIN_3 /\ X_2 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~S_0 /\ ~S_1 /\ ~S_2 /\ ~X_0 /\ ~X_1 /\ ~Y_0 /\ ~Y_1 \/ S_0 /\ S_1 /\ S_2 /\ X_0 /\ X_1 /\ X_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~Y_0 /\ ~Y_1 /\ ~Y_2 \/ S_0 /\ S_1 /\ S_2 /\ X_0 /\ X_1 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~X_2 /\ ~Y_0 /\ ~Y_1 \/ S_0 /\ S_1 /\ S_2 /\ X_0 /\ X_2 /\ Y_1 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~X_1 /\ ~Y_0 /\ ~Y_2 \/ S_0 /\ S_1 /\ S_2 /\ X_0 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~X_1 /\ ~X_2 /\ ~Y_0 \/ S_0 /\ S_1 /\ S_2 /\ X_1 /\ X_2 /\ Y_0 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~X_0 /\ ~Y_1 /\ ~Y_2 \/ S_0 /\ S_1 /\ S_2 /\ X_1 /\ Y_0 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~X_0 /\ ~X_2 /\ ~Y_1 \/ S_0 /\ S_1 /\ S_2 /\ X_2 /\ Y_0 /\ Y_1 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~X_0 /\ ~X_1 /\ ~Y_2 \/ S_0 /\ S_1 /\ S_2 /\ Y_0 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~X_0 /\ ~X_1 /\ ~X_2 \/ S_0 /\ S_1 /\ X_0 /\ X_1 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_2 /\ ~X_2 /\ ~Y_0 /\ ~Y_1 /\ ~Y_2 \/ S_0 /\ S_1 /\ X_0 /\ Y_1 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_2 /\ ~X_1 /\ ~X_2 /\ ~Y_0 /\ ~Y_2 \/ S_0 /\ S_1 /\ X_1 /\ Y_0 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_2 /\ ~X_0 /\ ~X_2 /\ ~Y_1 /\ ~Y_2 \/ S_0 /\ S_1 /\ Y_0 /\ Y_1 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_2 /\ ~X_0 /\ ~X_1 /\ ~X_2 /\ ~Y_2 \/ S_0 /\ S_2 /\ X_0 /\ X_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_1 /\ ~X_1 /\ ~Y_0 /\ ~Y_1 /\ ~Y_2 \/ S_0 /\ S_2 /\ X_0 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_1 /\ ~X_1 /\ ~X_2 /\ ~Y_0 /\ ~Y_1 \/ S_0 /\ S_2 /\ X_2 /\ Y_0 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_1 /\ ~X_0 /\ ~X_1 /\ ~Y_1 /\ ~Y_2 \/ S_0 /\ S_2 /\ Y_0 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_1 /\ ~X_0 /\ ~X_1 /\ ~X_2 /\ ~Y_1 \/ S_0 /\ X_0 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_1 /\ ~S_2 /\ ~X_1 /\ ~X_2 /\ ~Y_0 /\ ~Y_1 /\ ~Y_2 \/ S_0 /\ Y_0 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_1 /\ ~S_2 /\ ~X_0 /\ ~X_1 /\ ~X_2 /\ ~Y_1 /\ ~Y_2 \/ S_1 /\ S_2 /\ X_1 /\ X_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~X_0 /\ ~Y_0 /\ ~Y_1 /\ ~Y_2 \/ S_1 /\ S_2 /\ X_1 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~X_0 /\ ~X_2 /\ ~Y_0 /\ ~Y_1 \/ S_1 /\ S_2 /\ X_2 /\ Y_1 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~X_0 /\ ~X_1 /\ ~Y_0 /\ ~Y_2 \/ S_1 /\ S_2 /\ Y_1 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~X_0 /\ ~X_1 /\ ~X_2 /\ ~Y_0 \/ S_1 /\ X_1 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~S_2 /\ ~X_0 /\ ~X_2 /\ ~Y_0 /\ ~Y_1 /\ ~Y_2 \/ S_1 /\ Y_1 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~S_2 /\ ~X_0 /\ ~X_1 /\ ~X_2 /\ ~Y_0 /\ ~Y_2 \/ S_2 /\ X_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~S_1 /\ ~X_0 /\ ~X_1 /\ ~Y_0 /\ ~Y_1 /\ ~Y_2 \/ S_2 /\ Y_2 /\ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~S_1 /\ ~X_0 /\ ~X_1 /\ ~X_2 /\ ~Y_0 /\ ~Y_1 \/ ~CIN_1 /\ ~CIN_2 /\ ~CIN_3 /\ ~S_0 /\ ~S_1 /\ ~S_2 /\ ~X_0 /\ ~X_1 /\ ~X_2 /\ ~Y_0 /\ ~Y_1 /\ ~Y_2>>
  
  ripple 3 CNF:
  <<(CIN_1 \/ S_1 \/ X_1 \/ ~Y_1) /\ (CIN_1 \/ S_1 \/ Y_1 \/ ~X_1) /\ (CIN_1 \/ X_1 \/ Y_1 \/ ~S_1) /\ (CIN_1 \/ X_1 \/ ~CIN_2) /\ (CIN_1 \/ Y_1 \/ ~CIN_2) /\ (CIN_1 \/ ~S_1 \/ ~X_1 \/ ~Y_1) /\ (CIN_1 \/ ~X_0 \/ ~Y_0) /\ (CIN_2 \/ S_2 \/ X_2 \/ ~Y_2) /\ (CIN_2 \/ S_2 \/ Y_2 \/ ~X_2) /\ (CIN_2 \/ X_2 \/ Y_2 \/ ~S_2) /\ (CIN_2 \/ X_2 \/ ~CIN_3) /\ (CIN_2 \/ Y_2 \/ ~CIN_3) /\ (CIN_2 \/ ~CIN_1 \/ ~X_1) /\ (CIN_2 \/ ~CIN_1 \/ ~Y_1) /\ (CIN_2 \/ ~S_2 \/ ~X_2 \/ ~Y_2) /\ (CIN_2 \/ ~X_1 \/ ~Y_1) /\ (CIN_3 \/ ~CIN_2 \/ ~X_2) /\ (CIN_3 \/ ~CIN_2 \/ ~Y_2) /\ (CIN_3 \/ ~X_2 \/ ~Y_2) /\ (S_0 \/ X_0 \/ ~Y_0) /\ (S_0 \/ Y_0 \/ ~X_0) /\ (S_1 \/ X_1 \/ Y_1 \/ ~CIN_1) /\ (S_1 \/ ~CIN_1 \/ ~X_1 \/ ~Y_1) /\ (S_2 \/ X_2 \/ Y_2 \/ ~CIN_2) /\ (S_2 \/ ~CIN_2 \/ ~X_2 \/ ~Y_2) /\ (X_0 \/ Y_0 \/ ~S_0) /\ (X_0 \/ ~CIN_1) /\ (X_1 \/ Y_1 \/ ~CIN_2) /\ (X_1 \/ ~CIN_1 \/ ~S_1 \/ ~Y_1) /\ (X_2 \/ Y_2 \/ ~CIN_3) /\ (X_2 \/ ~CIN_2 \/ ~S_2 \/ ~Y_2) /\ (Y_0 \/ ~CIN_1) /\ (Y_1 \/ ~CIN_1 \/ ~S_1 \/ ~X_1) /\ (Y_2 \/ ~CIN_2 \/ ~S_2 \/ ~X_2) /\ (~S_0 \/ ~X_0 \/ ~Y_0)>>
  number of variables: 12
  number of clauses:   35
  
  
  ripple 3 DEF CNF:
  <<(CIN_1 \/ p_3 \/ p_4) /\ (CIN_1 \/ p_6 \/ ~p_7) /\ (CIN_1 \/ p_7 \/ ~p_6) /\ (CIN_1 \/ ~p_11) /\ (CIN_1 \/ ~p_3 \/ ~p_4) /\ (CIN_2 \/ p_12 \/ p_13) /\ (CIN_2 \/ p_15 \/ ~p_16) /\ (CIN_2 \/ p_16 \/ ~p_15) /\ (CIN_2 \/ ~p_12 \/ ~p_13) /\ (CIN_2 \/ ~p_20) /\ (CIN_3 \/ p_21 \/ p_22) /\ (CIN_3 \/ ~p_21 \/ ~p_22) /\ (S_0 \/ p_1 \/ p_2) /\ (S_0 \/ ~p_1 \/ ~p_2) /\ (S_1 \/ p_7 \/ p_8) /\ (S_1 \/ ~p_7 \/ ~p_8) /\ (S_2 \/ p_16 \/ p_17) /\ (S_2 \/ ~p_16 \/ ~p_17) /\ (X_0 \/ Y_0 \/ ~p_1) /\ (X_0 \/ p_1 \/ ~Y_0) /\ (X_0 \/ ~p_3) /\ (X_1 \/ Y_1 \/ ~p_10) /\ (X_1 \/ Y_1 \/ ~p_6) /\ (X_1 \/ p_6 \/ ~Y_1) /\ (X_1 \/ ~p_9) /\ (X_2 \/ Y_2 \/ ~p_15) /\ (X_2 \/ Y_2 \/ ~p_19) /\ (X_2 \/ p_15 \/ ~Y_2) /\ (X_2 \/ ~p_18) /\ (Y_0 \/ p_1 \/ ~X_0) /\ (Y_0 \/ ~p_3) /\ (Y_1 \/ p_6 \/ ~X_1) /\ (Y_1 \/ ~p_9) /\ (Y_2 \/ p_15 \/ ~X_2) /\ (Y_2 \/ ~p_18) /\ (p_1 \/ ~S_0 \/ ~p_2) /\ (p_10 \/ ~X_1) /\ (p_10 \/ ~Y_1) /\ (p_10 \/ ~p_11) /\ (p_11 \/ p_9 \/ ~p_12) /\ (p_11 \/ ~CIN_1 \/ ~p_10) /\ (p_12 \/ ~CIN_2 \/ ~p_13) /\ (p_12 \/ ~p_11) /\ (p_12 \/ ~p_9) /\ (p_13 \/ ~CIN_2 \/ ~p_12) /\ (p_13 \/ ~p_14) /\ (p_14 \/ ~p_13 \/ ~p_8) /\ (p_14 \/ ~p_24) /\ (p_15 \/ p_16 \/ ~CIN_2) /\ (p_16 \/ ~S_2 \/ ~p_17) /\ (p_17 \/ ~S_2 \/ ~p_16) /\ (p_17 \/ ~p_23) /\ (p_18 \/ p_20 \/ ~p_21) /\ (p_18 \/ ~X_2 \/ ~Y_2) /\ (p_19 \/ ~X_2) /\ (p_19 \/ ~Y_2) /\ (p_19 \/ ~p_20) /\ (p_2 \/ ~S_0 \/ ~p_1) /\ (p_2 \/ ~p_5) /\ (p_20 \/ ~CIN_2 \/ ~p_19) /\ (p_21 \/ ~CIN_3 \/ ~p_22) /\ (p_21 \/ ~p_18) /\ (p_21 \/ ~p_20) /\ (p_22 \/ ~CIN_3 \/ ~p_21) /\ (p_22 \/ ~p_23) /\ (p_23 \/ ~p_17 \/ ~p_22) /\ (p_23 \/ ~p_24) /\ (p_24 \/ ~p_14 \/ ~p_23) /\ (p_24 \/ ~p_25) /\ p_25 /\ (p_25 \/ ~p_24 \/ ~p_5) /\ (p_3 \/ ~CIN_1 \/ ~p_4) /\ (p_3 \/ ~X_0 \/ ~Y_0) /\ (p_4 \/ ~CIN_1 \/ ~p_3) /\ (p_4 \/ ~p_5) /\ (p_5 \/ ~p_2 \/ ~p_4) /\ (p_5 \/ ~p_25) /\ (p_6 \/ p_7 \/ ~CIN_1) /\ (p_7 \/ ~S_1 \/ ~p_8) /\ (p_8 \/ ~S_1 \/ ~p_7) /\ (p_8 \/ ~p_14) /\ (p_9 \/ ~X_1 \/ ~Y_1) /\ (~CIN_1 \/ ~p_6 \/ ~p_7) /\ (~CIN_2 \/ ~p_15 \/ ~p_16) /\ (~X_0 \/ ~Y_0 \/ ~p_1) /\ (~X_1 \/ ~Y_1 \/ ~p_6) /\ (~X_2 \/ ~Y_2 \/ ~p_15)>>
  number of variables: 37
  number of clauses:   87
  
  
  ripple 3 DEF CNF OPT:
  <<(CIN_1 \/ p_3 \/ p_4) /\ (CIN_1 \/ p_5 \/ ~p_6) /\ (CIN_1 \/ p_6 \/ ~p_5) /\ (CIN_1 \/ ~p_10) /\ (CIN_1 \/ ~p_3 \/ ~p_4) /\ (CIN_2 \/ p_11 \/ p_12) /\ (CIN_2 \/ p_13 \/ ~p_14) /\ (CIN_2 \/ p_14 \/ ~p_13) /\ (CIN_2 \/ ~p_11 \/ ~p_12) /\ (CIN_2 \/ ~p_18) /\ (CIN_3 \/ p_19 \/ p_20) /\ (CIN_3 \/ ~p_19 \/ ~p_20) /\ (S_0 \/ p_1 \/ p_2) /\ (S_0 \/ ~p_1 \/ ~p_2) /\ (S_1 \/ p_6 \/ p_7) /\ (S_1 \/ ~p_6 \/ ~p_7) /\ (S_2 \/ p_14 \/ p_15) /\ (S_2 \/ ~p_14 \/ ~p_15) /\ (X_0 \/ Y_0 \/ ~p_1) /\ (X_0 \/ p_1 \/ ~Y_0) /\ (X_0 \/ ~p_3) /\ (X_1 \/ Y_1 \/ ~p_5) /\ (X_1 \/ Y_1 \/ ~p_9) /\ (X_1 \/ p_5 \/ ~Y_1) /\ (X_1 \/ ~p_8) /\ (X_2 \/ Y_2 \/ ~p_13) /\ (X_2 \/ Y_2 \/ ~p_17) /\ (X_2 \/ p_13 \/ ~Y_2) /\ (X_2 \/ ~p_16) /\ (Y_0 \/ p_1 \/ ~X_0) /\ (Y_0 \/ ~p_3) /\ (Y_1 \/ p_5 \/ ~X_1) /\ (Y_1 \/ ~p_8) /\ (Y_2 \/ p_13 \/ ~X_2) /\ (Y_2 \/ ~p_16) /\ (p_1 \/ ~S_0 \/ ~p_2) /\ (p_10 \/ p_8 \/ ~p_11) /\ (p_10 \/ ~CIN_1 \/ ~p_9) /\ (p_11 \/ ~CIN_2 \/ ~p_12) /\ (p_11 \/ ~p_10) /\ (p_11 \/ ~p_8) /\ p_12 /\ (p_12 \/ ~CIN_2 \/ ~p_11) /\ (p_13 \/ p_14 \/ ~CIN_2) /\ (p_14 \/ ~S_2 \/ ~p_15) /\ p_15 /\ (p_15 \/ ~S_2 \/ ~p_14) /\ (p_16 \/ p_18 \/ ~p_19) /\ (p_16 \/ ~X_2 \/ ~Y_2) /\ (p_17 \/ ~X_2) /\ (p_17 \/ ~Y_2) /\ (p_17 \/ ~p_18) /\ (p_18 \/ ~CIN_2 \/ ~p_17) /\ (p_19 \/ ~CIN_3 \/ ~p_20) /\ (p_19 \/ ~p_16) /\ (p_19 \/ ~p_18) /\ p_2 /\ (p_2 \/ ~S_0 \/ ~p_1) /\ p_20 /\ (p_20 \/ ~CIN_3 \/ ~p_19) /\ (p_3 \/ ~CIN_1 \/ ~p_4) /\ (p_3 \/ ~X_0 \/ ~Y_0) /\ p_4 /\ (p_4 \/ ~CIN_1 \/ ~p_3) /\ (p_5 \/ p_6 \/ ~CIN_1) /\ (p_6 \/ ~S_1 \/ ~p_7) /\ p_7 /\ (p_7 \/ ~S_1 \/ ~p_6) /\ (p_8 \/ ~X_1 \/ ~Y_1) /\ (p_9 \/ ~X_1) /\ (p_9 \/ ~Y_1) /\ (p_9 \/ ~p_10) /\ (~CIN_1 \/ ~p_5 \/ ~p_6) /\ (~CIN_2 \/ ~p_13 \/ ~p_14) /\ (~X_0 \/ ~Y_0 \/ ~p_1) /\ (~X_1 \/ ~Y_1 \/ ~p_5) /\ (~X_2 \/ ~Y_2 \/ ~p_13)>>
  number of variables: 32
  number of clauses:   77
  
  
  carryselect 1 1
  <<((((s0_0 <=> ~(x_0 <=> y_0)) /\ (c0_1 <=> x_0 /\ y_0)) /\ (s1_0 <=> x_0 <=> y_0) /\ (c1_1 <=> x_0 /\ y_0 \/ x_0 \/ y_0)) /\ (c_1 <=> ~c_0 /\ c0_1 \/ c_0 /\ c1_1) /\ (s_0 <=> ~c_0 /\ s0_0 \/ c_0 /\ s1_0)) /\ (c_1 <=> ~c_1 /\ c0_1 \/ c_1 /\ c1_1)>>
  number of variables: 9
  
  
  carryselect 2 1
  <<((((s0_0 <=> ~(x_0 <=> y_0)) /\ (c0_1 <=> x_0 /\ y_0)) /\ (s1_0 <=> x_0 <=> y_0) /\ (c1_1 <=> x_0 /\ y_0 \/ x_0 \/ y_0)) /\ (c_1 <=> ~c_0 /\ c0_1 \/ c_0 /\ c1_1) /\ (s_0 <=> ~c_0 /\ s0_0 \/ c_0 /\ s1_0)) /\ ((((s0_1 <=> ~(x_1 <=> y_1)) /\ (c0_2 <=> x_1 /\ y_1)) /\ (s1_1 <=> x_1 <=> y_1) /\ (c1_2 <=> x_1 /\ y_1 \/ x_1 \/ y_1)) /\ (c_2 <=> ~c_1 /\ c0_2 \/ c_1 /\ c1_2) /\ (s_1 <=> ~c_1 /\ s0_1 \/ c_1 /\ s1_1)) /\ (c_2 <=> ~c_2 /\ c0_2 \/ c_2 /\ c1_2)>>
  number of variables: 17
  
  
  carryselect 3 1
  <<((((s0_0 <=> ~(x_0 <=> y_0)) /\ (c0_1 <=> x_0 /\ y_0)) /\ (s1_0 <=> x_0 <=> y_0) /\ (c1_1 <=> x_0 /\ y_0 \/ x_0 \/ y_0)) /\ (c_1 <=> ~c_0 /\ c0_1 \/ c_0 /\ c1_1) /\ (s_0 <=> ~c_0 /\ s0_0 \/ c_0 /\ s1_0)) /\ ((((s0_1 <=> ~(x_1 <=> y_1)) /\ (c0_2 <=> x_1 /\ y_1)) /\ (s1_1 <=> x_1 <=> y_1) /\ (c1_2 <=> x_1 /\ y_1 \/ x_1 \/ y_1)) /\ (c_2 <=> ~c_1 /\ c0_2 \/ c_1 /\ c1_2) /\ (s_1 <=> ~c_1 /\ s0_1 \/ c_1 /\ s1_1)) /\ ((((s0_2 <=> ~(x_2 <=> y_2)) /\ (c0_3 <=> x_2 /\ y_2)) /\ (s1_2 <=> x_2 <=> y_2) /\ (c1_3 <=> x_2 /\ y_2 \/ x_2 \/ y_2)) /\ (c_3 <=> ~c_2 /\ c0_3 \/ c_2 /\ c1_3) /\ (s_2 <=> ~c_2 /\ s0_2 \/ c_2 /\ s1_2)) /\ (c_3 <=> ~c_3 /\ c0_3 \/ c_3 /\ c1_3)>>
  number of variables: 25
  
  
  carryselect 3 2
  <<(((((s0_0 <=> ~(x_0 <=> y_0)) /\ (c0_1 <=> x_0 /\ y_0)) /\ (s0_1 <=> ~(~(x_1 <=> y_1) <=> c0_1)) /\ (c0_2 <=> x_1 /\ y_1 \/ (x_1 \/ y_1) /\ c0_1)) /\ ((s1_0 <=> x_0 <=> y_0) /\ (c1_1 <=> x_0 /\ y_0 \/ x_0 \/ y_0)) /\ (s1_1 <=> ~(~(x_1 <=> y_1) <=> c1_1)) /\ (c1_2 <=> x_1 /\ y_1 \/ (x_1 \/ y_1) /\ c1_1)) /\ (c_2 <=> ~c_0 /\ c0_2 \/ c_0 /\ c1_2) /\ (s_0 <=> ~c_0 /\ s0_0 \/ c_0 /\ s1_0) /\ (s_1 <=> ~c_0 /\ s0_1 \/ c_0 /\ s1_1)) /\ (((s0_2 <=> ~(x_2 <=> y_2)) /\ (c0_3 <=> x_2 /\ y_2)) /\ (s1_2 <=> x_2 <=> y_2) /\ (c1_3 <=> x_2 /\ y_2 \/ x_2 \/ y_2)) /\ (c_3 <=> ~c_2 /\ c0_3 \/ c_2 /\ c1_3) /\ (s_2 <=> ~c_2 /\ s0_2 \/ c_2 /\ s1_2)>>
  number of variables: 24
  
  
  equivalence of ripplecarry2 <=> carryselect21
  number of variables: 21
  true
  
  
  equivalence of ripplecarry2 <=> carryselect22
  number of variables: 20
  true
  
  
  equivalence of ripplecarry3 <=> carryselect32
  number of variables: 30
  (too large for naive tautology prover)


