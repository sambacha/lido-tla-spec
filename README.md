# lido-tla-spec

`lido` tla spec for node operators 

### Node Operator Algo's

```haskell
/* SelectCandidates */
procedure SelectCandidates(branch)
ActiveSet{} ← SelectActive(branch)
SortByAge(ActiveSet)
CandidateSet{} ← ActiveSet[0:Nc−1]
while InactiveRounds(CandidateSet[0]) ≥ Nc do
CandidateSet[0] ← Inactive
CandidateSet[Nc ] ← ActiveSet[Nc ]
ShiftLeft(CandidateSet,1)
return CandidateSet
```

#### SelectEndorsers

```haskell
/* SelectEndorsers */
procedure SelectEndorsers(branch)
ActiveNodes{} ← SelectActive(branch)
foreach node ∈ ActiveNodes do
if EnrollmentAge(node) < Te then
ActiveNodes = ActiveNodes \node
EndorserSet ← RandomSampling(Seedr−d , ActiveNodes)
return EndorserSet
```

#### SelectActive

```dhall
procedure SelectActive(branch)
iterBlock ← Top(branch)
i ← 0
ActiveSet{} ← ∅
while i < Ta do
i ← i + 1
BlockEndorsers ← GetEndorsers(iterBlock)
foreach Endorser ∈ BlockEndorsers do
if Endorser < ActiveSet then
ActiveSet ← ActiveSet ∪ Endorser
iterBlock ← Next(iterBlock)
return ActiveSet
```

#### SelectBranch

```dhall
/* SelectBranch */
procedure SelectBranch(Branches{})
foreach branch ∈ Branches{} do
if VerifyBranch(branch) , true then
Branches ← Branches \branch
Branches ← SortByLength(Branches)
Longest{} ← SelectLongest(Branches)
if |Longest| = 1 then
return Longest[0]
else
Selected ← Longest[0]
counter ← 1
while counter < |Longest | do
current ← Longest[counter]
Divergent ← GetFork(Selected,current)
if LeaderAge(Selected, Divergent) < LeaderAge(current, Divergent) then
Selected ← current
if LeaderAge(Selected, Divergent) = LeaderAge(current, Divergent) then
if Binary(Selected,Divergent) < Binary(current, Divergent) then
Selected ← current
return Selected


#### VerifyBranch

```dhall
/* VerifyBranch */
procedure VerifyBranch(currentBranch)
prevBlock ← Genesis(currentBranch)
iterBlock ← Next(prevBlock, currentBranch)
currentBlock ← Top(currentBranch)
while iterBlock , CurrentBlock do
if Hash(prevBlock) , prevHash(iterBlock) then
return false
iterLeader ← Leader(iterBlock)
if iterLeader < SelectCandidates(currentBranch[0, iterBlock]) then
return false
intent ← GetIntent(iterBlock)
if GetTxHash(intent) , Hash(GetTx(iterBlock)) then
return false
counter ← 0
foreach endorsement ∈ Endorsements(iterBlock) do
if VerifyEndorsement(endorsement,iterBlock) , true then
return false
counter ← counter+1
if counter < q then
return false
if VerifyVRF(iterBlock) , true then
return false
foreach enrollment ∈ Enrollments(iterBlock) do
if verify(enrollment) , true then
return false
prevBlock ← iterBlock
iterBlock ← Next(iterBlock, currentBranch)
return true
```

#### VerifyEndorsement

```dhall
/* VerifyEndorsement */
procedure VerifyEndorsement(endorsement, block, branch)
endorser ← GetEndorser(endorsement)
intent ← GetIntent(block)
leader ← GetLeader(block)
if GetChainID(endorsement) , GetChainID(block) then
return false
if endorser < SelectEndorsers(branch[0, block]) then
return false
if hash(intent) , GetIntentHash(endorsement) then
return false
if hash(leader) , GetLeaderHash(endorsement) then
return false
signature ← GetSignature(endorsement)
body ← GetBody(endorsement)
return VerifySignature(signature, body, endorser)
```
