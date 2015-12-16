---- MODULE MC ----
EXTENDS IdGeneratorByteCode, TLC

\* CONSTANT definitions @modelParameterConstants:0NumberOfProcesses
const_1449843210758102000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1Locking
const_1449843210769103000 == 
FALSE
----

\* Constant expression definition @modelExpressionEval
const_expr_1449843210779104000 == 
SubSeq(<<4,5,6,7>>, 1, Len(<<4,5,6,7>>)-1)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1449843210779104000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1449843210789105000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1449843210800106000 ==
IdGeneratorInvariant
----
=============================================================================
\* Modification History
\* Created Fri Dec 11 09:13:30 EST 2015 by balopat
