From ITree Require Import ITree.

Import ITreeNotations.
Open Scope itree.

Section OGS_naive.

  (* We consider domains of:
     - (Opponent) configurations [conf]: ~corresponds to Γ
     - Opponent actions [OA]
     - Player actions [PA]
   *)
  Variable conf OA PA : Type.

  (* Given the current configuration and an opponent action,
     a strategy describes how the player can react by either:
     - silently diverging
     - playing an action, leading to a new configuration
   *)
  Variable Strat : conf -> OA -> itree void1 (PA * conf).

  (* We observe the alternating trace of actions
     by player and opponent *)
  Variant E : Type -> Type :=
    | StepO : E OA
    | StepP (op : PA) : E unit.

  Definition embed {F} : void1 ~> F :=
    fun _ (x: void1 _) => match x with end.

  (* Naive encoding of the OGS over a given strategy [Strat] *)
  Definition OGS : conf -> itree E unit :=
    fun conf_init =>
      rec (fun c =>
             oa <- trigger StepO;;
             '(pa, c') <- translate embed (Strat c oa);;
             trigger (StepP pa);;
             call c')
          conf_init.

End OGS_naive.

