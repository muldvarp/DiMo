(* Is it possible to cover every cell on an n x n chess board with at most k queens? *)

MODELS QueensCover(n,k)
PROPOSITIONS D
PARAMETERS n: {3,..}, k: {1,..} WITH k <= n
FORMULAS 
  QueensCover(n,k) = EveryFieldCovered(n) & ExactlykQueensPlaced(n,k)

  EveryFieldCovered(n) = FORALL i:{1,..,n}. FORALL j:{1,..,n}. D(i,j) | HasQueenInRow(i,j,n) | HasQueenInColumn(i,j,n) | HasQueenOnDiagUp(i,j,n) | HasQueenOnDiagDown(i,j,n)

  HasQueenInRow(i,j,n)      = FORSOME h:{1,..,n}-{i}. D(h,j)
  HasQueenInColumn(i,j,n)   = FORSOME h:{1,..,n}-{j}. D(i,h)
  HasQueenOnDiagUp(x,y,n)   = FORSOME h:{ MAX {(x-y)+1,1}, .., MIN {n,(x-y)+n} } - {x}. D(h,h+(y-x))
  HasQueenOnDiagDown(x,y,n) = FORSOME h:{ MAX {(x+y)-n,1}, .., MIN {n,(x+y)-1} } - {x}. D(h,(x+y)-h)

  ExactlykQueensPlaced(n,k) = P(0,0) & 
                              (FORALL i:{0,..,n*n}. -P(i,k+1)) &
                              FORALL i:{0,..,n*n-1}. FORALL h:{0,..,k}. P(i,h) -> P(i+1,h) & (D((i/n)+1, (i MOD n)+1) -> P(i+1,h+1))


