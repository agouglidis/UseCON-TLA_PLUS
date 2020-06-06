--------------------------- MODULE preUseCON_Pol1 ---------------------------

EXTENDS Integers, TLC

\* DECLARATION OF SUBJECT OBJECT ACTION
\* They are declared only by their id attribute
\* which is constant in the model
CONSTANTS SID, OID, AID
VARIABLES U 

\* DECLARATION OF UID ATTRIBUTE
UID==(SID \X AID \X OID)

\* DECLARATION OF USTATUS ATTRIBUTE
USTATUS == {"init","requested","activated","denied","completed"}

\* DECLARATION OF USES
USES == [status:USTATUS]

\* DECLARATION OF PolicyNeutral PREDICATE
PolicyNeutral(u) == RandomElement({TRUE,FALSE})

\* Type checking
TypeOK==U \in [UID -> USES]

\* Policy1
SameSO(u1,u2)== /\ u1[1]=u2[1]
                /\ u1[3]=u2[3]

\* Original Policy1
\* action aid1 -> non disclosure agreement action
\* action aid2 -> read action
\* 
\* usage with aid1 is activated always
\* any other usage is activated only if previously 
\* a usage with aid1 is already completed for the same subject, object combination
Policy1(u1) ==  \/ u1[2]="aid1"
                \/ \E u2 \in UID : (
                        /\ SameSO(u1,u2)
                        /\ u2[2] = "aid1"
                        /\ U[u2].status = "completed")
                            
\* Modified Policy1
\* 
\* Compare with original Policy 1 does not check that usage with action aid1 will be completed on the same subject object
\* Therefore any other usage than aid1 will be activated if any aid1 action is completed for any object
MPolicy1(u1) ==  \/ u1[2]="aid1"
                 \/ \E u2 \in UID : (
                        /\ u1[1] = u2[1]
                        /\ u2[2] = "aid1"           
                        /\ U[u2].status = "completed")


\*        PRE AUTHORIZATION MODEL 
\* (***************************************************************************
Init == U=[uid \in UID|->[status|->"init"]]
        
vars == <<U>>

Request ==    /\ \E uid \in UID:  
                    /\ U[uid].status="init"
                    /\ U' = [U EXCEPT ![uid].status = "requested"]

preEvaluate == \E uid \in UID:  
                    /\ U[uid].status="requested"
                    /\ U'= [U EXCEPT ![uid].status=
                             IF (MPolicy1(uid)) THEN "activated"     
                                ELSE "denied"]

Complete == \E uid \in UID:  
                /\ U[uid].status="activated"
                /\ U' = [U EXCEPT ![uid].status="completed"]
                                              
Next== Request  \/ preEvaluate \/ Complete

Spec == /\ Init /\ [][Next]_vars  /\ WF_vars(Next)

\* Safety Properties Pre                          
Safety_Pre_Completed == [] (\forall uid_n \in UID: U[uid_n].status="completed" => []  ~ ( U[uid_n].status="init" \/ U[uid_n].status="requested"  \/ U[uid_n].status="activated" \/ U[uid_n].status="denied" ))
Safety_Pre_Activated == [] (\forall uid_n \in UID: U[uid_n].status="activated" => []  ~ ( U[uid_n].status="init" \/ U[uid_n].status="requested"  \/ U[uid_n].status="denied" ))
Safety_Pre_Denied == [] (\forall uid_n \in UID: U[uid_n].status="denied" => []  ~ ( U[uid_n].status="init" \/ U[uid_n].status="requested"  \/ U[uid_n].status="activated" \/ U[uid_n].status="completed" ))
Safety_Pre_Requested == [] ( \forall uid_n \in UID: U[uid_n].status="requested" => []  ~ ( U[uid_n].status="init" ))

\* Liveness properties Pre-                      
Liveness_Pre_Init == \forall uid_n \in UID: U[uid_n].status="init" ~> U[uid_n].status="requested"
Liveness_Pre_Requested == \forall uid_n \in UID: U[uid_n].status="requested" ~> ( U[uid_n].status="activated" \/ U[uid_n].status="denied" )
Liveness_Pre_Activated == \forall uid_n \in UID: U[uid_n].status="activated" ~> U[uid_n].status="completed" 

\* ---------------------------------------------------------------
\* Policy1 Properties

\* Safety
\* 
\* for every view action (aid2) that is activated it must exists an 
\* completed non-disclosure action (aid1) for the same s,o combination
Safety1 == \forall uid1 \in UID : (uid1[2]#"aid1" /\ U[uid1].status="activated" => (\E uid2 \in UID : uid2[2]="aid1" /\ U[uid2].status="completed" /\ SameSO(uid1,uid2)))

=============================================================================
