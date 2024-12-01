Require Import List.
Import ListNotations.
Import Bool.
Import Nat.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Open Scope string_scope.



Definition DList (A : Type) := { l : list A & NoDup l}.

Example dlist_example : DList nat.
Proof.
  exists [1; 2].
  constructor.
    - simpl. intro. destruct H; [inversion H; assumption | assumption].
    - simpl. constructor.
      + intro. simpl in H. assumption.
      + constructor.
Qed.

Inductive Typ : Set :=
| t_nat
| t_bool
| t_unit.

Inductive Exp : Set -> Set :=
| add        : Exp nat  -> Exp nat -> Exp nat
| ifthenelse : Exp bool -> Exp nat -> Exp nat -> Exp nat
| lt         : Exp nat  -> Exp nat -> Exp bool
| printf     : (n : string) -> printftype n -> Exp unit
where
Fixpoint printftype (s : string) : Exp :=
  match s with
  | "%d" ++ xs => prod (Exp bool) (printftype xs)
  | String _ xs => printftype xs
  | _ => Exp unit
  end.

  