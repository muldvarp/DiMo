SATISFIABLE NQueens(n)
PROPOSITIONS D
PARAMETERS n: {1,..}
FORMULAS 
  NQueens(n) = AtLeastOneInEachRow(n)
             & AtMostOneInEachRow(n)
             & AtMostOneInEachColumn(n)
             & AtMostOneInEachDiagUp(n)
             & AtMostOneInEachDiagDown(n)
	         
  AtLeastOneInEachRow(n)     = 
    FORALL i: {1,..,n}. FORSOME j: {1,..,n}. D(i,j)
    
  AtMostOneInEachRow(n)      = 
    FORALL i: {1,..,n}. FORALL j: {1,..,n-1}. 
      D(i,j) -> FORALL k: {j+1,..,n}. -D(i,k)
    
  AtMostOneInEachColumn(n)   = 
    FORALL i: {1,..,n-1}. FORALL j: {1,..,n}. 
      D(i,j) -> FORALL k: {i+1,..,n}. -D(k,j)
    
  AtMostOneInEachDiagUp(n)   = 
    FORALL i: {1,..,n-1}. FORALL j: {1,..,n-1}. 
      D(i,j) -> FORALL k: {1,..,MIN {n-i,n-j}}. -D(i+k,j+k)
    
  AtMostOneInEachDiagDown(n) = 
    FORALL i: {1,..,n-1}. FORALL j: {2,..,n}. 
      D(i,j) -> FORALL k: {1,..,MIN {n-i,j-1}}. -D(i+k,j-k)
