Require Export VariableDefinitions.
Require Export Hlist.
Require Export Logic.

Module TypeSystem(E : Embedding).
Module APRHL := APRHL(E).

Import E.
Import APRHL.
Import APRHL.SEM.
Import APRHL.SEM.LAP.
Import APRHL.SEM.LAP.RP.
Import APRHL.SEM.LAP.RP.PP.
Import APRHL.SEM.LAP.RP.PP.MP.
Import APRHL.SEM.LAP.RP.PP.MP.UP.

Definition dist_relation (t : tau) (v1 v2 : tau_denote t) (z : Z) : Prop :=
  match t as t' return (tau_denote t' -> tau_denote t'-> Prop) with
  | t_int => fun v1 v2 => ((v1 - v2)%Z <= z)%Z
  | t_bool => fun v1 v2 => if (z =? 0)%Z then (v1 = v2) else True
  end v1 v2.

Inductive env {ts : list tau} : Type :=
| env_nil : env
| env_cons : forall {t}, var t ts -> Z -> env -> env.

Program Fixpoint env_update {t ts} (e : env) (x : var t ts) (d : Z) : env :=
  match e with
  | env_nil => env_cons x d env_nil
  | env_cons _ x' d' e' =>
    if member_eq tau_eqdec x' x
    then env_cons x d e'
    else env_cons x' d' (env_update e' x d)
  end.

Program Fixpoint env_remove {t ts} (e : env) (x : var t ts) : env :=
  match e with
  | env_nil => env_nil
  | env_cons _ x' d' e' =>
    if member_eq tau_eqdec x' x
    then env_remove e' x
    else env_cons x' d' (env_remove e' x)
  end.

Program Fixpoint denote_env {ts} (e : env) : memory_relation ts :=
  match e with
  | env_nil =>
    fun m1 m2 => True
  | env_cons _t x d tl =>
    fun m1 m2 => (dist_relation _t (h_get m1 x) (h_get m2 x) d)
                 /\ (denote_env _ m1 m2)
  end.

Module Test.
Example ts := [t_int; t_int; t_bool]%list.
Example x := m_first t_int [t_int; t_bool]%list.
Example y := m_next t_int (m_first t_int [t_bool]%list).
Example z := m_next t_int (m_next t_int (m_first t_bool []%list)).

Example env1 :=
  env_cons x 1 (env_cons y 2 (env_cons z 0 env_nil)).
Example env2 :=
  env_cons x 1 (env_cons y 2 (env_cons z 5 env_nil)).

Eval simpl in (denote_env env1).
Eval simpl in (denote_env env2).
Eval compute in (env_update env1 x 10).
End Test.

Definition typechecker {ts} := @env ts -> cmd ts -> (R * @env ts)%type.

(* The theorem we need to prove to establish the validity of a typing rule in apRHL *)
Definition typechecker_valid {ts} (r : @typechecker ts) :=
  forall e_pre c,
    let eps := fst (r e_pre c) in
    let e_post := snd (r e_pre c) in
    c ~_(eps) c : denote_env e_pre ==> denote_env e_post.

Definition typesystem {ts} := @env ts -> cmd ts -> R -> @env ts -> Prop.

(* The theorem we need to prove to show a typesystem is sound *)
Definition typesystem_valid {ts} (T : @typesystem ts) :=
  forall pre post c eps,
    T pre c eps post -> c ~_(eps) c : denote_env pre ==> denote_env post.

End TypeSystem.