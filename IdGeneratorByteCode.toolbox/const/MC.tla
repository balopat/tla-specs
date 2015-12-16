---- MODULE MC ----
EXTENDS IdGeneratorByteCode, TLC

\* CONSTANT definitions @modelParameterConstants:0NumberOfProcesses
const_144984225988075000 == 
1
----

\* Constant expression definition @modelExpressionEval
const_expr_144984225989176000 == 
SubSeq(<<4,5,6,7>>, 1, Len(<<4,5,6,7>>)-1)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_144984225989176000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_144984225990277000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_144984225991378000 ==
IdGeneratorInvariant
----
=============================================================================
\* Modification History
\* Created Fri Dec 11 08:57:39 EST 2015 by balopat
