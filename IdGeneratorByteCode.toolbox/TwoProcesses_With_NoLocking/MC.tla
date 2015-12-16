---- MODULE MC ----
EXTENDS IdGeneratorByteCode, TLC

\* CONSTANT definitions @modelParameterConstants:0NumberOfProcesses
const_1450029005678176000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1Locking
const_1450029005689177000 == 
FALSE
----

\* Constant expression definition @modelExpressionEval
const_expr_1450029005700178000 == 
SubSeq(<<4,5,6,7>>, 1, Len(<<4,5,6,7>>)-1)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1450029005700178000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1450029005711179000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1450029005722180000 ==
IdGeneratorInvariant
----
=============================================================================
\* Modification History
\* Created Sun Dec 13 12:50:05 EST 2015 by balopat
