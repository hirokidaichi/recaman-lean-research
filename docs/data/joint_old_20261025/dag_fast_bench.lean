/- Generated proof DAG. Numeric input SHA256 716ea518a9592ae1ef2dbc8930d6f51fb8e2be1503c5ff0f641c5aff4977ba6d. -/
import Recaman.FourEventFast
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option Elab.async false
namespace Recaman.FourEventData
open Recaman.FourNonsuppliedData Recaman.FourEventProof

private def s_12835 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,true,true,true,false,true],10,10,4⟩
private theorem c_12835 : Checked s_12835 := by
  apply checked_of_children s_12835 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)
#check c_12835

private def s_12836 : State := ⟨[false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true,true,true],10,10,4⟩
private theorem c_12836 : Checked s_12836 := by
  apply checked_of_children s_12836 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12830 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,true,true,true],9,9,4⟩
private theorem c_12830 : Checked s_12830 := by
  apply checked_of_children s_12830 [s_12835]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12835

private def s_12831 : State := ⟨[false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,true],9,9,4⟩
private theorem c_12831 : Checked s_12831 := by
  apply checked_of_children s_12831 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12832 : State := ⟨[false,false,false,false,true,false,false,false,true,true,true,true,false,true,true,true,false,false,true],9,10,4⟩
private theorem c_12832 : Checked s_12832 := by
  apply checked_of_children s_12832 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12833 : State := ⟨[false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true,true],9,10,4⟩
private theorem c_12833 : Checked s_12833 := by
  apply checked_of_children s_12833 [s_12836]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12836

private def s_12834 : State := ⟨[false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,true,true,true,true,false,true],9,12,4⟩
private theorem c_12834 : Checked s_12834 := by
  apply checked_of_children s_12834 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12773 : State := ⟨[false,true,false,false,false,false,false,true,true,true,true,false,true,true,true],8,7,4⟩
private theorem c_12773 : Checked s_12773 := by
  apply checked_of_children s_12773 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12774 : State := ⟨[false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,7,4⟩
private theorem c_12774 : Checked s_12774 := by
  apply checked_of_children s_12774 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12775 : State := ⟨[false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,8,4⟩
private theorem c_12775 : Checked s_12775 := by
  apply checked_of_children s_12775 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12776 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,true,true],8,6,4⟩
private theorem c_12776 : Checked s_12776 := by
  apply checked_of_children s_12776 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12777 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,false,true,true,true],8,7,4⟩
private theorem c_12777 : Checked s_12777 := by
  apply checked_of_children s_12777 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12778 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,true],8,5,4⟩
private theorem c_12778 : Checked s_12778 := by
  apply checked_of_children s_12778 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12779 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,true],8,6,4⟩
private theorem c_12779 : Checked s_12779 := by
  apply checked_of_children s_12779 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12780 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,true],8,7,4⟩
private theorem c_12780 : Checked s_12780 := by
  apply checked_of_children s_12780 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12781 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,false,true],8,8,4⟩
private theorem c_12781 : Checked s_12781 := by
  apply checked_of_children s_12781 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12782 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,false,false,true],8,9,4⟩
private theorem c_12782 : Checked s_12782 := by
  apply checked_of_children s_12782 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12783 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,false,false,false,true],8,10,4⟩
private theorem c_12783 : Checked s_12783 := by
  apply checked_of_children s_12783 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12784 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,false,false,false,false,true],8,11,4⟩
private theorem c_12784 : Checked s_12784 := by
  apply checked_of_children s_12784 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12785 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,false,false,false,false,false,true],8,12,4⟩
private theorem c_12785 : Checked s_12785 := by
  apply checked_of_children s_12785 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12786 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,false,false,false,false,false,false,true],8,13,4⟩
private theorem c_12786 : Checked s_12786 := by
  apply checked_of_children s_12786 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12787 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,false,false,false,false,false,false,false,true],8,14,4⟩
private theorem c_12787 : Checked s_12787 := by
  apply checked_of_children s_12787 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12788 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,false,false,false,false,false,false,false,false,true],8,15,4⟩
private theorem c_12788 : Checked s_12788 := by
  apply checked_of_children s_12788 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12789 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,true],8,16,4⟩
private theorem c_12789 : Checked s_12789 := by
  apply checked_of_children s_12789 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12790 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true],8,17,4⟩
private theorem c_12790 : Checked s_12790 := by
  apply checked_of_children s_12790 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12791 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true],8,18,4⟩
private theorem c_12791 : Checked s_12791 := by
  apply checked_of_children s_12791 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12792 : State := ⟨[false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],8,19,4⟩
private theorem c_12792 : Checked s_12792 := by
  apply checked_of_children s_12792 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12793 : State := ⟨[true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],8,19,4⟩
private theorem c_12793 : Checked s_12793 := by
  apply checked_of_children s_12793 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12794 : State := ⟨[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],8,19,4⟩
private theorem c_12794 : Checked s_12794 := by
  apply checked_of_children s_12794 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12795 : State := ⟨[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],8,19,4⟩
private theorem c_12795 : Checked s_12795 := by
  apply checked_of_children s_12795 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12796 : State := ⟨[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],8,19,4⟩
private theorem c_12796 : Checked s_12796 := by
  apply checked_of_children s_12796 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12797 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,true,false,true],8,7,4⟩
private theorem c_12797 : Checked s_12797 := by
  apply checked_of_children s_12797 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12798 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,true,true],8,6,4⟩
private theorem c_12798 : Checked s_12798 := by
  apply checked_of_children s_12798 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12799 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,true,true],8,7,4⟩
private theorem c_12799 : Checked s_12799 := by
  apply checked_of_children s_12799 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12800 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,true,true],8,8,4⟩
private theorem c_12800 : Checked s_12800 := by
  apply checked_of_children s_12800 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12801 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,true,true],8,9,4⟩
private theorem c_12801 : Checked s_12801 := by
  apply checked_of_children s_12801 [s_12830]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12830

private def s_12802 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,true,true,true],8,10,4⟩
private theorem c_12802 : Checked s_12802 := by
  apply checked_of_children s_12802 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12803 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,true,true,true],8,11,4⟩
private theorem c_12803 : Checked s_12803 := by
  apply checked_of_children s_12803 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12804 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,true,true,true],8,12,4⟩
private theorem c_12804 : Checked s_12804 := by
  apply checked_of_children s_12804 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12805 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,true,true,true],8,13,4⟩
private theorem c_12805 : Checked s_12805 := by
  apply checked_of_children s_12805 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12806 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true,true],8,14,4⟩
private theorem c_12806 : Checked s_12806 := by
  apply checked_of_children s_12806 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12807 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,true,true,true],8,15,4⟩
private theorem c_12807 : Checked s_12807 := by
  apply checked_of_children s_12807 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12808 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,true,true,true],8,16,4⟩
private theorem c_12808 : Checked s_12808 := by
  apply checked_of_children s_12808 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12809 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true],8,17,4⟩
private theorem c_12809 : Checked s_12809 := by
  apply checked_of_children s_12809 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12810 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true],8,18,4⟩
private theorem c_12810 : Checked s_12810 := by
  apply checked_of_children s_12810 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12811 : State := ⟨[false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true],8,19,4⟩
private theorem c_12811 : Checked s_12811 := by
  apply checked_of_children s_12811 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12812 : State := ⟨[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true],8,19,4⟩
private theorem c_12812 : Checked s_12812 := by
  apply checked_of_children s_12812 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12813 : State := ⟨[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true],8,19,4⟩
private theorem c_12813 : Checked s_12813 := by
  apply checked_of_children s_12813 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12814 : State := ⟨[false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true],8,8,4⟩
private theorem c_12814 : Checked s_12814 := by
  apply checked_of_children s_12814 [s_12831]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12831

private def s_12815 : State := ⟨[false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,9,4⟩
private theorem c_12815 : Checked s_12815 := by
  apply checked_of_children s_12815 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12816 : State := ⟨[false,false,false,false,true,false,false,false,true,true,true,true,false,true,true,true],8,8,4⟩
private theorem c_12816 : Checked s_12816 := by
  apply checked_of_children s_12816 [s_12832]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12832

private def s_12817 : State := ⟨[false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,10,4⟩
private theorem c_12817 : Checked s_12817 := by
  apply checked_of_children s_12817 [s_12833]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12833

private def s_12818 : State := ⟨[false,false,false,false,false,true,false,false,true,true,true,true,false,true,true,true],8,8,4⟩
private theorem c_12818 : Checked s_12818 := by
  apply checked_of_children s_12818 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12819 : State := ⟨[false,false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,11,4⟩
private theorem c_12819 : Checked s_12819 := by
  apply checked_of_children s_12819 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12820 : State := ⟨[false,false,false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,12,4⟩
private theorem c_12820 : Checked s_12820 := by
  apply checked_of_children s_12820 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12821 : State := ⟨[false,false,false,false,false,false,false,false,true,true,true,false,true,true,true,true,false,true],8,10,4⟩
private theorem c_12821 : Checked s_12821 := by
  apply checked_of_children s_12821 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12822 : State := ⟨[false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,13,4⟩
private theorem c_12822 : Checked s_12822 := by
  apply checked_of_children s_12822 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12823 : State := ⟨[false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,14,4⟩
private theorem c_12823 : Checked s_12823 := by
  apply checked_of_children s_12823 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12824 : State := ⟨[false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,true,true,true,true],8,11,4⟩
private theorem c_12824 : Checked s_12824 := by
  apply checked_of_children s_12824 [s_12834]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12834

private def s_12825 : State := ⟨[false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,15,4⟩
private theorem c_12825 : Checked s_12825 := by
  apply checked_of_children s_12825 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12826 : State := ⟨[false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,16,4⟩
private theorem c_12826 : Checked s_12826 := by
  apply checked_of_children s_12826 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12827 : State := ⟨[false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,17,4⟩
private theorem c_12827 : Checked s_12827 := by
  apply checked_of_children s_12827 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12828 : State := ⟨[false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,18,4⟩
private theorem c_12828 : Checked s_12828 := by
  apply checked_of_children s_12828 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12829 : State := ⟨[false,false,false,false,false,false,true,true,true,false,false,false,false,true,true,true,true,false,true],8,19,4⟩
private theorem c_12829 : Checked s_12829 := by
  apply checked_of_children s_12829 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12507 : State := ⟨[false,true,false,true,false,false,false,true,true,true,true,false,true],7,6,4⟩
private theorem c_12507 : Checked s_12507 := by
  apply checked_of_children s_12507 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12508 : State := ⟨[false,true,false,false,false,true,true,true,false,true,true,true],7,5,4⟩
private theorem c_12508 : Checked s_12508 := by
  apply checked_of_children s_12508 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12509 : State := ⟨[false,true,false,false,false,false,false,true,true,true,true,false,true,true],7,7,4⟩
private theorem c_12509 : Checked s_12509 := by
  apply checked_of_children s_12509 [s_12773]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12773

private def s_12510 : State := ⟨[false,false,true,true,true,false,false,true,true,true,false,true],7,5,4⟩
private theorem c_12510 : Checked s_12510 := by
  apply checked_of_children s_12510 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12511 : State := ⟨[false,false,true,true,true,false,false,false,false,true,true,true,true],7,6,4⟩
private theorem c_12511 : Checked s_12511 := by
  apply checked_of_children s_12511 [s_12774]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12774

private def s_12512 : State := ⟨[false,false,true,false,false,true,false,false,true,true,true,true,false,true],7,7,4⟩
private theorem c_12512 : Checked s_12512 := by
  apply checked_of_children s_12512 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12513 : State := ⟨[false,false,false,true,true,true,true,false,true,true,true],7,4,4⟩
private theorem c_12513 : Checked s_12513 := by
  apply checked_of_children s_12513 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12514 : State := ⟨[false,false,false,true,true,true,false,true,false,true,true,true],7,5,4⟩
private theorem c_12514 : Checked s_12514 := by
  apply checked_of_children s_12514 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12515 : State := ⟨[false,false,false,true,true,true,false,false,true,true,true,false,true],7,6,4⟩
private theorem c_12515 : Checked s_12515 := by
  apply checked_of_children s_12515 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12516 : State := ⟨[false,false,false,true,true,true,false,false,false,false,true,true,true,true],7,7,4⟩
private theorem c_12516 : Checked s_12516 := by
  apply checked_of_children s_12516 [s_12775]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12775

private def s_12517 : State := ⟨[false,false,false,true,true,false,false,false,true,true,true,true,false,true],7,7,4⟩
private theorem c_12517 : Checked s_12517 := by
  apply checked_of_children s_12517 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12518 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,true],7,6,4⟩
private theorem c_12518 : Checked s_12518 := by
  apply checked_of_children s_12518 [s_12776]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12776

private def s_12519 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,true],7,7,4⟩
private theorem c_12519 : Checked s_12519 := by
  apply checked_of_children s_12519 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12520 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,false,true],7,8,4⟩
private theorem c_12520 : Checked s_12520 := by
  apply checked_of_children s_12520 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12521 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,false,false,true],7,9,4⟩
private theorem c_12521 : Checked s_12521 := by
  apply checked_of_children s_12521 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12522 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,false,false,false,true],7,10,4⟩
private theorem c_12522 : Checked s_12522 := by
  apply checked_of_children s_12522 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12523 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,false,false,false,false,true],7,11,4⟩
private theorem c_12523 : Checked s_12523 := by
  apply checked_of_children s_12523 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12524 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,false,false,false,false,false,true],7,12,4⟩
private theorem c_12524 : Checked s_12524 := by
  apply checked_of_children s_12524 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12525 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,true],7,13,4⟩
private theorem c_12525 : Checked s_12525 := by
  apply checked_of_children s_12525 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12526 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,true],7,14,4⟩
private theorem c_12526 : Checked s_12526 := by
  apply checked_of_children s_12526 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12527 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,true],7,15,4⟩
private theorem c_12527 : Checked s_12527 := by
  apply checked_of_children s_12527 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12528 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,true],7,16,4⟩
private theorem c_12528 : Checked s_12528 := by
  apply checked_of_children s_12528 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12529 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,true],7,17,4⟩
private theorem c_12529 : Checked s_12529 := by
  apply checked_of_children s_12529 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12530 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true],7,18,4⟩
private theorem c_12530 : Checked s_12530 := by
  apply checked_of_children s_12530 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12531 : State := ⟨[true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12531 : Checked s_12531 := by
  apply checked_of_children s_12531 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12532 : State := ⟨[true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12532 : Checked s_12532 := by
  apply checked_of_children s_12532 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12533 : State := ⟨[true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12533 : Checked s_12533 := by
  apply checked_of_children s_12533 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12534 : State := ⟨[false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12534 : Checked s_12534 := by
  apply checked_of_children s_12534 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12535 : State := ⟨[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12535 : Checked s_12535 := by
  apply checked_of_children s_12535 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12536 : State := ⟨[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12536 : Checked s_12536 := by
  apply checked_of_children s_12536 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12537 : State := ⟨[false,false,false,true,false,false,true,true,true,true,false,false,true,true],7,7,4⟩
private theorem c_12537 : Checked s_12537 := by
  apply checked_of_children s_12537 [s_12777]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12777

private def s_12538 : State := ⟨[false,false,false,true,false,false,true,true,true,false,true,true,true],7,6,4⟩
private theorem c_12538 : Checked s_12538 := by
  apply checked_of_children s_12538 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12539 : State := ⟨[false,false,false,true,false,false,true,true,true,false,true,true,false,true],7,7,4⟩
private theorem c_12539 : Checked s_12539 := by
  apply checked_of_children s_12539 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12540 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true],7,5,4⟩
private theorem c_12540 : Checked s_12540 := by
  apply checked_of_children s_12540 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12541 : State := ⟨[false,false,false,false,true,true,true,true,true,true,false,false,true],7,6,4⟩
private theorem c_12541 : Checked s_12541 := by
  apply checked_of_children s_12541 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12542 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,true],7,5,3⟩
private theorem c_12542 : Checked s_12542 := by
  apply checked_of_children s_12542 [s_12778,s_12779,s_12780,s_12781,s_12782,s_12783,s_12784,s_12785,s_12786,s_12787,s_12788,s_12789,s_12790,s_12791,s_12792,s_12793,s_12794,s_12795,s_12796,s_12796]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact c_12778
    · exact c_12779
    · exact c_12780
    · exact c_12781
    · exact c_12782
    · exact c_12783
    · exact c_12784
    · exact c_12785
    · exact c_12786
    · exact c_12787
    · exact c_12788
    · exact c_12789
    · exact c_12790
    · exact c_12791
    · exact c_12792
    · exact c_12793
    · exact c_12794
    · exact c_12795
    · exact c_12796
    · exact c_12796

private def s_12543 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,true],7,6,4⟩
private theorem c_12543 : Checked s_12543 := by
  apply checked_of_children s_12543 [s_12797]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12797

private def s_12544 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,true],7,7,4⟩
private theorem c_12544 : Checked s_12544 := by
  apply checked_of_children s_12544 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12545 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,false,true],7,8,4⟩
private theorem c_12545 : Checked s_12545 := by
  apply checked_of_children s_12545 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12546 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,true],7,9,4⟩
private theorem c_12546 : Checked s_12546 := by
  apply checked_of_children s_12546 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12547 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,true],7,10,4⟩
private theorem c_12547 : Checked s_12547 := by
  apply checked_of_children s_12547 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12548 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,true],7,11,4⟩
private theorem c_12548 : Checked s_12548 := by
  apply checked_of_children s_12548 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12549 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,true],7,12,4⟩
private theorem c_12549 : Checked s_12549 := by
  apply checked_of_children s_12549 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12550 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,false,true],7,13,4⟩
private theorem c_12550 : Checked s_12550 := by
  apply checked_of_children s_12550 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12551 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,false,false,true],7,14,4⟩
private theorem c_12551 : Checked s_12551 := by
  apply checked_of_children s_12551 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12552 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,false,false,false,true],7,15,4⟩
private theorem c_12552 : Checked s_12552 := by
  apply checked_of_children s_12552 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12553 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,true],7,16,4⟩
private theorem c_12553 : Checked s_12553 := by
  apply checked_of_children s_12553 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12554 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true],7,17,4⟩
private theorem c_12554 : Checked s_12554 := by
  apply checked_of_children s_12554 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12555 : State := ⟨[false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,18,4⟩
private theorem c_12555 : Checked s_12555 := by
  apply checked_of_children s_12555 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12556 : State := ⟨[true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12556 : Checked s_12556 := by
  apply checked_of_children s_12556 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12557 : State := ⟨[false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12557 : Checked s_12557 := by
  apply checked_of_children s_12557 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12558 : State := ⟨[true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12558 : Checked s_12558 := by
  apply checked_of_children s_12558 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12559 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,true],7,6,4⟩
private theorem c_12559 : Checked s_12559 := by
  apply checked_of_children s_12559 [s_12798]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12798

private def s_12560 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,true],7,7,4⟩
private theorem c_12560 : Checked s_12560 := by
  apply checked_of_children s_12560 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12561 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,false,true],7,8,4⟩
private theorem c_12561 : Checked s_12561 := by
  apply checked_of_children s_12561 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12562 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,false,false,true],7,9,4⟩
private theorem c_12562 : Checked s_12562 := by
  apply checked_of_children s_12562 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12563 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,false,false,false,true],7,10,4⟩
private theorem c_12563 : Checked s_12563 := by
  apply checked_of_children s_12563 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12564 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,false,false,false,false,true],7,11,4⟩
private theorem c_12564 : Checked s_12564 := by
  apply checked_of_children s_12564 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12565 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,false,false,false,false,false,true],7,12,4⟩
private theorem c_12565 : Checked s_12565 := by
  apply checked_of_children s_12565 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12566 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,false,false,false,false,false,false,true],7,13,4⟩
private theorem c_12566 : Checked s_12566 := by
  apply checked_of_children s_12566 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12567 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,false,false,false,false,false,false,false,true],7,14,4⟩
private theorem c_12567 : Checked s_12567 := by
  apply checked_of_children s_12567 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12568 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true],7,15,4⟩
private theorem c_12568 : Checked s_12568 := by
  apply checked_of_children s_12568 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12569 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,false,false,false,false,false,false,false,false,false,true],7,16,4⟩
private theorem c_12569 : Checked s_12569 := by
  apply checked_of_children s_12569 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12570 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,false,false,false,false,false,false,false,false,false,false,true],7,17,4⟩
private theorem c_12570 : Checked s_12570 := by
  apply checked_of_children s_12570 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12571 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true],7,18,4⟩
private theorem c_12571 : Checked s_12571 := by
  apply checked_of_children s_12571 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12572 : State := ⟨[true,false,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12572 : Checked s_12572 := by
  apply checked_of_children s_12572 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12573 : State := ⟨[false,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12573 : Checked s_12573 := by
  apply checked_of_children s_12573 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12574 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,true],7,7,4⟩
private theorem c_12574 : Checked s_12574 := by
  apply checked_of_children s_12574 [s_12799]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12799

private def s_12575 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,false,true],7,8,4⟩
private theorem c_12575 : Checked s_12575 := by
  apply checked_of_children s_12575 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12576 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,false,false,true],7,9,4⟩
private theorem c_12576 : Checked s_12576 := by
  apply checked_of_children s_12576 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12577 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,false,false,false,true],7,10,4⟩
private theorem c_12577 : Checked s_12577 := by
  apply checked_of_children s_12577 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12578 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,false,false,false,false,true],7,11,4⟩
private theorem c_12578 : Checked s_12578 := by
  apply checked_of_children s_12578 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12579 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,false,false,false,false,false,true],7,12,4⟩
private theorem c_12579 : Checked s_12579 := by
  apply checked_of_children s_12579 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12580 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,false,false,false,false,false,false,true],7,13,4⟩
private theorem c_12580 : Checked s_12580 := by
  apply checked_of_children s_12580 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12581 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,false,false,false,false,false,false,false,true],7,14,4⟩
private theorem c_12581 : Checked s_12581 := by
  apply checked_of_children s_12581 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12582 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false,true],7,15,4⟩
private theorem c_12582 : Checked s_12582 := by
  apply checked_of_children s_12582 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12583 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false,false,true],7,16,4⟩
private theorem c_12583 : Checked s_12583 := by
  apply checked_of_children s_12583 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12584 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,true],7,17,4⟩
private theorem c_12584 : Checked s_12584 := by
  apply checked_of_children s_12584 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12585 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,true],7,18,4⟩
private theorem c_12585 : Checked s_12585 := by
  apply checked_of_children s_12585 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12586 : State := ⟨[true,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12586 : Checked s_12586 := by
  apply checked_of_children s_12586 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12587 : State := ⟨[false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12587 : Checked s_12587 := by
  apply checked_of_children s_12587 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12588 : State := ⟨[true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12588 : Checked s_12588 := by
  apply checked_of_children s_12588 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12589 : State := ⟨[false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12589 : Checked s_12589 := by
  apply checked_of_children s_12589 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12590 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,true],7,8,4⟩
private theorem c_12590 : Checked s_12590 := by
  apply checked_of_children s_12590 [s_12800]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12800

private def s_12591 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,false,true],7,9,4⟩
private theorem c_12591 : Checked s_12591 := by
  apply checked_of_children s_12591 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12592 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,false,false,true],7,10,4⟩
private theorem c_12592 : Checked s_12592 := by
  apply checked_of_children s_12592 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12593 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,false,false,false,true],7,11,4⟩
private theorem c_12593 : Checked s_12593 := by
  apply checked_of_children s_12593 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12594 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,false,false,false,false,true],7,12,4⟩
private theorem c_12594 : Checked s_12594 := by
  apply checked_of_children s_12594 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12595 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,false,false,false,false,false,true],7,13,4⟩
private theorem c_12595 : Checked s_12595 := by
  apply checked_of_children s_12595 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12596 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,false,false,false,false,false,false,true],7,14,4⟩
private theorem c_12596 : Checked s_12596 := by
  apply checked_of_children s_12596 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12597 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,false,false,false,false,false,false,false,true],7,15,4⟩
private theorem c_12597 : Checked s_12597 := by
  apply checked_of_children s_12597 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12598 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,false,false,false,false,false,false,false,false,true],7,16,4⟩
private theorem c_12598 : Checked s_12598 := by
  apply checked_of_children s_12598 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12599 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,true],7,17,4⟩
private theorem c_12599 : Checked s_12599 := by
  apply checked_of_children s_12599 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12600 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,true],7,18,4⟩
private theorem c_12600 : Checked s_12600 := by
  apply checked_of_children s_12600 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12601 : State := ⟨[true,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12601 : Checked s_12601 := by
  apply checked_of_children s_12601 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12602 : State := ⟨[false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12602 : Checked s_12602 := by
  apply checked_of_children s_12602 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12603 : State := ⟨[true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12603 : Checked s_12603 := by
  apply checked_of_children s_12603 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12604 : State := ⟨[false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12604 : Checked s_12604 := by
  apply checked_of_children s_12604 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12605 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,true],7,9,4⟩
private theorem c_12605 : Checked s_12605 := by
  apply checked_of_children s_12605 [s_12801]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12801

private def s_12606 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,false,true],7,10,4⟩
private theorem c_12606 : Checked s_12606 := by
  apply checked_of_children s_12606 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12607 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,false,false,true],7,11,4⟩
private theorem c_12607 : Checked s_12607 := by
  apply checked_of_children s_12607 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12608 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,false,false,false,true],7,12,4⟩
private theorem c_12608 : Checked s_12608 := by
  apply checked_of_children s_12608 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12609 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,false,false,false,false,true],7,13,4⟩
private theorem c_12609 : Checked s_12609 := by
  apply checked_of_children s_12609 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12610 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,false,false,false,false,false,true],7,14,4⟩
private theorem c_12610 : Checked s_12610 := by
  apply checked_of_children s_12610 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12611 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,false,false,false,false,false,false,true],7,15,4⟩
private theorem c_12611 : Checked s_12611 := by
  apply checked_of_children s_12611 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12612 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,false,false,false,false,false,false,false,true],7,16,4⟩
private theorem c_12612 : Checked s_12612 := by
  apply checked_of_children s_12612 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12613 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,true],7,17,4⟩
private theorem c_12613 : Checked s_12613 := by
  apply checked_of_children s_12613 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12614 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,true],7,18,4⟩
private theorem c_12614 : Checked s_12614 := by
  apply checked_of_children s_12614 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12615 : State := ⟨[true,false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12615 : Checked s_12615 := by
  apply checked_of_children s_12615 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12616 : State := ⟨[false,true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12616 : Checked s_12616 := by
  apply checked_of_children s_12616 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12617 : State := ⟨[true,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12617 : Checked s_12617 := by
  apply checked_of_children s_12617 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12618 : State := ⟨[false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12618 : Checked s_12618 := by
  apply checked_of_children s_12618 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12619 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,true,true],7,10,4⟩
private theorem c_12619 : Checked s_12619 := by
  apply checked_of_children s_12619 [s_12802]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12802

private def s_12620 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,true,false,true],7,11,4⟩
private theorem c_12620 : Checked s_12620 := by
  apply checked_of_children s_12620 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12621 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,true,false,false,true],7,12,4⟩
private theorem c_12621 : Checked s_12621 := by
  apply checked_of_children s_12621 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12622 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,true,false,false,false,true],7,13,4⟩
private theorem c_12622 : Checked s_12622 := by
  apply checked_of_children s_12622 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12623 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,true,false,false,false,false,true],7,14,4⟩
private theorem c_12623 : Checked s_12623 := by
  apply checked_of_children s_12623 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12624 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,true,false,false,false,false,false,true],7,15,4⟩
private theorem c_12624 : Checked s_12624 := by
  apply checked_of_children s_12624 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12625 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,true,false,false,false,false,false,false,true],7,16,4⟩
private theorem c_12625 : Checked s_12625 := by
  apply checked_of_children s_12625 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12626 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,true,false,false,false,false,false,false,false,true],7,17,4⟩
private theorem c_12626 : Checked s_12626 := by
  apply checked_of_children s_12626 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12627 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true],7,18,4⟩
private theorem c_12627 : Checked s_12627 := by
  apply checked_of_children s_12627 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12628 : State := ⟨[true,false,true,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12628 : Checked s_12628 := by
  apply checked_of_children s_12628 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12629 : State := ⟨[false,true,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12629 : Checked s_12629 := by
  apply checked_of_children s_12629 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12630 : State := ⟨[true,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12630 : Checked s_12630 := by
  apply checked_of_children s_12630 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12631 : State := ⟨[false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12631 : Checked s_12631 := by
  apply checked_of_children s_12631 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12632 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,true,true],7,11,4⟩
private theorem c_12632 : Checked s_12632 := by
  apply checked_of_children s_12632 [s_12803]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12803

private def s_12633 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,true,false,true],7,12,4⟩
private theorem c_12633 : Checked s_12633 := by
  apply checked_of_children s_12633 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12634 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,true,false,false,true],7,13,4⟩
private theorem c_12634 : Checked s_12634 := by
  apply checked_of_children s_12634 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12635 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,true,false,false,false,true],7,14,4⟩
private theorem c_12635 : Checked s_12635 := by
  apply checked_of_children s_12635 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12636 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,true,false,false,false,false,true],7,15,4⟩
private theorem c_12636 : Checked s_12636 := by
  apply checked_of_children s_12636 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12637 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,true,false,false,false,false,false,true],7,16,4⟩
private theorem c_12637 : Checked s_12637 := by
  apply checked_of_children s_12637 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12638 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,true],7,17,4⟩
private theorem c_12638 : Checked s_12638 := by
  apply checked_of_children s_12638 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12639 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,false,true],7,18,4⟩
private theorem c_12639 : Checked s_12639 := by
  apply checked_of_children s_12639 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12640 : State := ⟨[true,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12640 : Checked s_12640 := by
  apply checked_of_children s_12640 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12641 : State := ⟨[false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12641 : Checked s_12641 := by
  apply checked_of_children s_12641 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12642 : State := ⟨[true,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12642 : Checked s_12642 := by
  apply checked_of_children s_12642 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12643 : State := ⟨[false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12643 : Checked s_12643 := by
  apply checked_of_children s_12643 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12644 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,true,true],7,12,4⟩
private theorem c_12644 : Checked s_12644 := by
  apply checked_of_children s_12644 [s_12804]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12804

private def s_12645 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,true,false,true],7,13,4⟩
private theorem c_12645 : Checked s_12645 := by
  apply checked_of_children s_12645 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12646 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,true,false,false,true],7,14,4⟩
private theorem c_12646 : Checked s_12646 := by
  apply checked_of_children s_12646 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12647 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,true,false,false,false,true],7,15,4⟩
private theorem c_12647 : Checked s_12647 := by
  apply checked_of_children s_12647 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12648 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,true,false,false,false,false,true],7,16,4⟩
private theorem c_12648 : Checked s_12648 := by
  apply checked_of_children s_12648 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12649 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,true,false,false,false,false,false,true],7,17,4⟩
private theorem c_12649 : Checked s_12649 := by
  apply checked_of_children s_12649 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12650 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,true,false,false,false,false,false,false,true],7,18,4⟩
private theorem c_12650 : Checked s_12650 := by
  apply checked_of_children s_12650 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12651 : State := ⟨[true,false,true,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12651 : Checked s_12651 := by
  apply checked_of_children s_12651 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12652 : State := ⟨[false,true,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12652 : Checked s_12652 := by
  apply checked_of_children s_12652 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12653 : State := ⟨[true,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12653 : Checked s_12653 := by
  apply checked_of_children s_12653 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12654 : State := ⟨[false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12654 : Checked s_12654 := by
  apply checked_of_children s_12654 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12655 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,true,true],7,13,4⟩
private theorem c_12655 : Checked s_12655 := by
  apply checked_of_children s_12655 [s_12805]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12805

private def s_12656 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,true,false,true],7,14,4⟩
private theorem c_12656 : Checked s_12656 := by
  apply checked_of_children s_12656 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12657 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,true,false,false,true],7,15,4⟩
private theorem c_12657 : Checked s_12657 := by
  apply checked_of_children s_12657 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12658 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,true,false,false,false,true],7,16,4⟩
private theorem c_12658 : Checked s_12658 := by
  apply checked_of_children s_12658 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12659 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,true,false,false,false,false,true],7,17,4⟩
private theorem c_12659 : Checked s_12659 := by
  apply checked_of_children s_12659 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12660 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,true,false,false,false,false,false,true],7,18,4⟩
private theorem c_12660 : Checked s_12660 := by
  apply checked_of_children s_12660 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12661 : State := ⟨[true,false,true,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12661 : Checked s_12661 := by
  apply checked_of_children s_12661 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12662 : State := ⟨[false,true,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12662 : Checked s_12662 := by
  apply checked_of_children s_12662 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12663 : State := ⟨[true,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12663 : Checked s_12663 := by
  apply checked_of_children s_12663 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12664 : State := ⟨[false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12664 : Checked s_12664 := by
  apply checked_of_children s_12664 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12665 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,true],7,14,4⟩
private theorem c_12665 : Checked s_12665 := by
  apply checked_of_children s_12665 [s_12806]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12806

private def s_12666 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,false,true],7,15,4⟩
private theorem c_12666 : Checked s_12666 := by
  apply checked_of_children s_12666 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12667 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,true],7,16,4⟩
private theorem c_12667 : Checked s_12667 := by
  apply checked_of_children s_12667 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12668 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,true],7,17,4⟩
private theorem c_12668 : Checked s_12668 := by
  apply checked_of_children s_12668 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12669 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true],7,18,4⟩
private theorem c_12669 : Checked s_12669 := by
  apply checked_of_children s_12669 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12670 : State := ⟨[true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,true],7,19,4⟩
private theorem c_12670 : Checked s_12670 := by
  apply checked_of_children s_12670 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12671 : State := ⟨[false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12671 : Checked s_12671 := by
  apply checked_of_children s_12671 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12672 : State := ⟨[true,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12672 : Checked s_12672 := by
  apply checked_of_children s_12672 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12673 : State := ⟨[false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12673 : Checked s_12673 := by
  apply checked_of_children s_12673 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12674 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,true,true],7,15,4⟩
private theorem c_12674 : Checked s_12674 := by
  apply checked_of_children s_12674 [s_12807]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12807

private def s_12675 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,true,false,true],7,16,4⟩
private theorem c_12675 : Checked s_12675 := by
  apply checked_of_children s_12675 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12676 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,true,false,false,true],7,17,4⟩
private theorem c_12676 : Checked s_12676 := by
  apply checked_of_children s_12676 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12677 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true],7,18,4⟩
private theorem c_12677 : Checked s_12677 := by
  apply checked_of_children s_12677 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12678 : State := ⟨[true,false,true,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true],7,19,4⟩
private theorem c_12678 : Checked s_12678 := by
  apply checked_of_children s_12678 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12679 : State := ⟨[false,true,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,true],7,19,4⟩
private theorem c_12679 : Checked s_12679 := by
  apply checked_of_children s_12679 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12680 : State := ⟨[true,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12680 : Checked s_12680 := by
  apply checked_of_children s_12680 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12681 : State := ⟨[false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12681 : Checked s_12681 := by
  apply checked_of_children s_12681 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12682 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,true,true],7,16,4⟩
private theorem c_12682 : Checked s_12682 := by
  apply checked_of_children s_12682 [s_12808]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12808

private def s_12683 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,true,false,true],7,17,4⟩
private theorem c_12683 : Checked s_12683 := by
  apply checked_of_children s_12683 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12684 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true],7,18,4⟩
private theorem c_12684 : Checked s_12684 := by
  apply checked_of_children s_12684 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12685 : State := ⟨[true,false,true,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true],7,19,4⟩
private theorem c_12685 : Checked s_12685 := by
  apply checked_of_children s_12685 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12686 : State := ⟨[false,true,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true],7,19,4⟩
private theorem c_12686 : Checked s_12686 := by
  apply checked_of_children s_12686 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12687 : State := ⟨[true,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,true],7,19,4⟩
private theorem c_12687 : Checked s_12687 := by
  apply checked_of_children s_12687 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12688 : State := ⟨[false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,true],7,19,4⟩
private theorem c_12688 : Checked s_12688 := by
  apply checked_of_children s_12688 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12689 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true],7,17,4⟩
private theorem c_12689 : Checked s_12689 := by
  apply checked_of_children s_12689 [s_12809]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12809

private def s_12690 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true],7,18,4⟩
private theorem c_12690 : Checked s_12690 := by
  apply checked_of_children s_12690 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12691 : State := ⟨[true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true],7,19,4⟩
private theorem c_12691 : Checked s_12691 := by
  apply checked_of_children s_12691 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12692 : State := ⟨[false,true,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true],7,19,4⟩
private theorem c_12692 : Checked s_12692 := by
  apply checked_of_children s_12692 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12693 : State := ⟨[true,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,true],7,19,4⟩
private theorem c_12693 : Checked s_12693 := by
  apply checked_of_children s_12693 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12694 : State := ⟨[false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,true],7,19,4⟩
private theorem c_12694 : Checked s_12694 := by
  apply checked_of_children s_12694 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12695 : State := ⟨[false,false,false,false,true,true,true,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true],7,18,4⟩
private theorem c_12695 : Checked s_12695 := by
  apply checked_of_children s_12695 [s_12810]
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    · exact c_12810

private def s_12696 : State := ⟨[true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true],7,19,4⟩
private theorem c_12696 : Checked s_12696 := by
  apply checked_of_children s_12696 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12697 : State := ⟨[false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true],7,19,4⟩
private theorem c_12697 : Checked s_12697 := by
  apply checked_of_children s_12697 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

private def s_12698 : State := ⟨[true,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true],7,19,4⟩
private theorem c_12698 : Checked s_12698 := by
  apply checked_of_children s_12698 []
  · decide
  · rw [Recaman.FourEventFast.successors_eq_fast]
    decide
  · intro t ht
    exact False.elim (List.not_mem_nil ht)

end Recaman.FourEventData
