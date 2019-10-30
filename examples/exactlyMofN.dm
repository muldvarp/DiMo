MODELS

  ExactlyMofN(n,m)
  
PROPOSITIONS
	A

PARAMETERS
	n : {1,..},
	m : NAT
        WITH m <= n

FORMULAS

  ExactlyMofN(n,m) = AtLeastMChosen(n,m) & AtMostMChosen(n,m)
  
  AtLeastMChosen(n,m) = B(n,m) & BsWellBehaved(n,m) & BsEndOk(m)

  BsWellBehaved(n,m) = FORALL i : {1,..,n}. FORALL j: {1,..,m}. B(i,j) -> ( (A(i) & B(i-1,j-1)) | B(i-1,j)) 
  BsEndOk(m)         = FORALL j : {1,..,m}. -B(0,j)

  AtMostMChosen(n,m) = AtLeastNminusMNotChosen(n,n-m)
  AtLeastNminusMNotChosen(n,m) = N(n,m) & NsWellBehaved(n,m) & NsEndOk(m)

  NsWellBehaved(n,m) = FORALL i : {1,..,n}. FORALL j: {1,..,m}. N(i,j) -> ( (-A(i) & N(i-1,j-1)) | N(i-1,j))
  NsEndOk(m)         = FORALL j : {1,..,m}. -N(0,j)

