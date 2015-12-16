---- MODULE MC ----
EXTENDS IdGeneratorByteCode, TLC

\* CONSTANT definitions @modelParameterConstants:0NumberOfProcesses
const_1450028985883167000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:1Locking
const_1450028985894168000 == 
TRUE
----

\* Constant expression definition @modelExpressionEval
const_expr_1450028985904169000 == 
SubSeq(<<4,5,6,7>>, 1, Len(<<4,5,6,7>>)-1)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1450028985904169000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1450028985915170000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1450028985927171000 ==
IdGeneratorInvariant
----
=============================================================================
\* Modification History
\* Created Sun Dec 13 12:49:45 EST 2015 by balopat
