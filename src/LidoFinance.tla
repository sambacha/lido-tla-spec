----------------------- MODULE LidoFinance ------------------------------------
EXTENDS Integers, Naturals, TLC, Sequences, FiniteSets

VARIABLES
  eth1,
  eth2,
  lidoprotocol,
  priceFeed,
  lidoParameters,
  lidoWithdrawls,
  roots

\*-----------------------

SumSeq(S) ==
  LET seq == S
      Sum[ i \in 1..Len(seq) ] == IF i = 1 THEN seq[i] ELSE seq[i] + Sum[i-1]
  IN IF seq = <<>> THEN 0 ELSE Sum[Len(seq)]

RECURSIVE SeqFromSet(_)
SeqFromSet(S) ==
  IF S = {} THEN << >>
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  << x >> \o SeqFromSet(S \ {x})

Range(s) == {s[x] : x \in DOMAIN s}

Hash(v) == CHOOSE n \in 1..5: TRUE

ASSUME(Hash(<<1>>) = Hash(<<1>>))
ASSUME(Hash(<<{1,2,3}>>) = Hash(<<{2,1,3,1}>>))

\*-----------------------

Init ==
  /\ eth1 = 1
  /\ eth2 = 2..3
  /\ lidoprotocol = 1..3
  /\ priceFeed = [c \in eth2 |-> <<>>]
  /\ lidoParameters = 1
  /\ roots = [c \in lidoprotocol |-> <<>>]
  /\ lidoWithdrawls = [c \in lidoprotocol |-> {}]

LidoParameters(c) ==
  /\ c # 1
  /\ Len(priceFeed[c]) < 5
  /\ priceFeed' = [priceFeed EXCEPT ![c] = priceFeed[c] \o <<[
      target |-> lidoprotocol, amount |-> 1, id |-> Hash(1..2)
     ]>>]
  /\ Print(<<"send", Len(priceFeed[c])>>, TRUE)
  /\ UNCHANGED <<eth1, eth2, lidoprotocol, roots, lidoParameters, lidoWithdrawls>>

LidoLiquidity(c) ==
  /\ c # 1
  /\ Len(roots[c]) < 20
  /\ SumSeq([x \in DOMAIN priceFeed[c] |-> priceFeed[c][x].amount]) > lidoParameters
  /\ Print(<<"commit">>, TRUE)
  /\ priceFeed' = [priceFeed EXCEPT ![c] = <<>>]
  /\ roots' = [k \in lidoprotocol |-> roots[k] \o <<Hash(priceFeed[c])>>]
  /\ UNCHANGED <<eth1, eth2, lidoprotocol, lidoParameters, lidoWithdrawls>>

LidoWithdrawls(dest) ==
  /\ \E source \in eth2:
    /\ Len(priceFeed[source]) > 0
    /\ \E x \in DOMAIN priceFeed[source] :
      /\ priceFeed[source][x].id \notin lidoWithdrawls[dest]
      /\ lidoWithdrawls' = [lidoWithdrawls EXCEPT ![dest] = lidoWithdrawls[dest] \cup {priceFeed[source][x].id}]
      /\ Print(<<"LidoWithdrawls", lidoWithdrawls'>>, TRUE)
    /\ UNCHANGED <<eth1, eth2, lidoprotocol, lidoParameters, priceFeed, roots>>

Next ==
  /\ \E c \in lidoprotocol :
      /\ \/ LidoParameters(c)
         \/ LidoLiquidity(c)
         \/ LidoWithdrawls(c)

AllHaveTransferRoots == /\ \A c \in lidoprotocol :
                            /\ Len(roots[c]) > 0
                            /\ \A k \in lidoprotocol: Range(roots[c]) \cap Range(roots[k]) # {}

AllHavelidoWithdrawls == /\ \A c \in lidoprotocol :
                                /\ Len(SeqFromSet(lidoWithdrawls[c])) > 0

EventuallyAllHaveTransferRoots == <>[]AllHaveTransferRoots
EventuallyAllHavelidoWithdrawls == <>[]AllHavelidoWithdrawls

vars == <<eth1, eth2, lidoprotocol, priceFeed, lidoParameters, roots, lidoWithdrawls>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Live == EventuallyAllHaveTransferRoots /\ EventuallyAllHavelidoWithdrawls
===============================================================================