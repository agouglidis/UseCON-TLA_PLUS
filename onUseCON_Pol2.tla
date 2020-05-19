--------------------------- MODULE onUseCON_Pol2 ---------------------------

EXTENDS Integers, TLC

\* DECLARATION OF SUBJECT OBJECT ACTION
\* They are declared only by their id attribute
\* which is constant in the model
CONSTANTS SID, OID, AID
VARIABLES U 

\* DECLARATION OF UID ATTRIBUTE
UID==(SID \X AID \X OID)

\* DECLARATION OF USTATUS ATTRIBUTE
USTATUS == {"init","requested","activated","terminated","completed"}

\* DECLARATION OF USES
USES == [status:USTATUS]

\* Type checking
TypeOK==U \in [UID -> USES]

\* Predicate for generic OnUseCON model
\* RandomElement({TRUE,FALSE})

\* Policy 2 Predicate
\* 
\* subject sid1 -> normal category
\* subject sid2 -> golden category
\*
\* when either is requested a usage of sid1 or sid2 is always activated (onActivate action)
\* 
\* if a usage from sid1 is activated on an object and  a usage from sid2 is activated on the same object
\* usage from sid1 is terminated in order for usage of sid2 to receive better QoS
Policy2(u1)==   \/ u1[1]="sid2"
                \/ 
                    /\ u1[1]="sid1"
                    /\ ~(\E u2 \in UID:
                            /\ u2[1]="sid2"
                            /\ u1[3]=u2[3]
                            /\ U[u2].status="activated")

\* Modified Policy2_1   
\* Compared with Policy 2 remove same object constraint and violates Liveness3
\* It violates property Liveness3 because now a usage from sid1 maybe terminated 
\* a usage from id2 is activated on another object                        
MPolicy2_1(u1)==   \/ u1[1]="sid2"
                   \/ 
                      /\ u1[1]="sid1"
                      /\ ~(\E u2 \in UID:
                            /\ u2[1]="sid2"
                            /\ U[u2].status="activated")

\* Tweaked Policy2_2  
\* Compared with Policy 2 remove that usages from sid2 are always completed
\* It violates property Liveness1 because now usages from sid2 from OnEvaluate action
MPolicy2_2(u1)==   
                    /\ u1[1]="sid1"
                    /\ ~(\E u2 \in UID:
                            /\ u2[1]="sid2"
                            /\ u1[3]=u2[3]
                            /\ U[u2].status="activated")
                            

\*        PRE AUTHORIZATION MODEL 
\* (***************************************************************************
Init == U=[uid \in UID|->[status|->"init"]]
               
vars == <<U>>

Request ==    /\ \E uid \in UID:  
                    /\ U[uid].status="init"
                    /\ U' = [U EXCEPT ![uid].status = "requested"]

onActivate == \E uid \in UID:  
                /\ U[uid].status="requested"
                /\ U' = [U EXCEPT ![uid].status="activated"]

onEvaluate == \E uid \in UID:  
                    /\ U[uid].status="activated"
                    /\ U'= [U EXCEPT ![uid].status=
                             IF (Policy2(uid)) THEN "activated"     
                                ELSE "terminated"]

Complete == \E uid \in UID:  
                /\ U[uid].status="activated"
                /\ U' = [U EXCEPT ![uid].status="completed"]
                                              
Next== Request  \/ onActivate \/ onEvaluate \/ Complete

Spec == /\ Init /\ [][Next]_vars  /\ WF_vars(Next)

\* Safety Properties On
Safety_On_Completed == [] (\forall uid_n \in UID: U[uid_n].status="completed" => []  ~ ( U[uid_n].status="init" \/ U[uid_n].status="requested"  \/ U[uid_n].status="activated" \/ U[uid_n].status="terminated" ))
Safety_On_Activated == [] (\forall uid_n \in UID: U[uid_n].status="activated" => []  ~ ( U[uid_n].status="init" \/ U[uid_n].status="requested"))
Safety_On_Terminated == [] (\forall uid_n \in UID: U[uid_n].status="terminated" => []  ~ ( U[uid_n].status="init" \/ U[uid_n].status="requested"  \/ U[uid_n].status="activated" \/ U[uid_n].status="completed" ))
Safety_On_Requested ==  [] (\forall uid_n \in UID: U[uid_n].status="requested" => []  ~ ( U[uid_n].status="init" ))

\* Liveness Properties On
Liveness_On_Init == \forall uid_n \in UID: U[uid_n].status="init" ~> U[uid_n].status="requested"
Liveness_On_Requested == \forall uid_n \in UID: U[uid_n].status="requested" ~> U[uid_n].status="activated" 
Liveness_On_Activated == \forall uid_n \in UID: U[uid_n].status="activated" ~> (U[uid_n].status="completed"  \/ U[uid_n].status="terminated" )

\* Policy 2 Properties
\* ------------------------------

\* Eventually all the usages from sid2 will be completed
Liveness1 == \forall uid \in UID: (uid[1]="sid2" /\ U[uid].status#"completed") ~> (U[uid].status="completed")
\* Eventually all the usages from sid1 will be either completed or terminated 
Liveness2 == \forall uid \in UID: (uid[1]="sid1" /\ (U[uid].status#"completed" \/ U[uid].status#"terminated")) ~> ( U[uid].status="completed" \/ U[uid].status="terminated")
\* if usages from sid2 already completed and the same time usages from sid1 is still requesting 
\* on the same object then in the future usages from sid1 will be completed
Liveness3 == \forall uid1,uid2 \in UID: uid1[3]=uid2[3] /\ uid1[1]="sid1" /\ uid2[1]="sid2" /\ U[uid1].status="requested" /\ U[uid2].status="completed" ~> U[uid1].status="completed"

=============================================================================
