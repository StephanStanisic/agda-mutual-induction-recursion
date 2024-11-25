Require Import List.
Import ListNotations.


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
