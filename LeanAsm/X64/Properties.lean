import LeanAsm.X64.Execution

/-! Register updates and unsigned ADD/ADC properties of the Lean execution model.
    These theorems do not establish equivalence with hardware or an ISA manual. -/

namespace LeanAsm.X64

theorem Size.trim_toNat (size : Size) (value : Word) :
    (size.trim value).toNat = value.toNat % 2 ^ size.bits := by
  simp only [Size.trim, BitVec.toNat_and, Size.mask, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2 ^ size.bits - 1 < 2 ^ 64 by cases size <;> decide)]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem Size.trim_lt (size : Size) (value : Word) :
    (size.trim value).toNat < 2 ^ size.bits := by
  rw [Size.trim_toNat]
  exact Nat.mod_lt _ (by cases size <;> decide)

@[simp] theorem Size.trim_idempotent (size : Size) (value : Word) :
    size.trim (size.trim value) = size.trim value := by
  simp [Size.trim, BitVec.and_assoc]

@[simp] theorem Size.trim_b64 (value : Word) : Size.b64.trim value = value := by
  apply BitVec.eq_of_toNat_eq
  simpa [Size.trim_toNat, Size.bits] using BitVec.toNat_mod_cancel value

theorem Reg.toNat_inj {a b : Reg} : a.toNat = b.toNat ↔ a = b := by
  cases a <;> cases b <;> decide

@[simp] theorem State.getReg_setReg_self (state : State) (reg : Reg) (value : Word) :
    (state.setReg reg value).getReg reg = value := by
  simp [State.getReg, State.setReg]

@[simp] theorem State.getReg_setReg_of_ne (state : State) (dst other : Reg)
    (value : Word) (h : dst ≠ other) :
    (state.setReg dst value).getReg other = state.getReg other := by
  simp [State.getReg, State.setReg, Reg.toNat_inj, h]

theorem State.getReg_writeReg_self (state : State) (size : Size) (reg : Reg)
    (value : Word) :
    (state.writeReg size reg value).getReg reg =
      if size == .b8 || size == .b16 then
        (state.getReg reg &&& ~~~size.mask) ||| size.trim value else size.trim value := by
  simp [State.writeReg]

@[simp] theorem State.getReg_writeReg_of_ne (state : State) (size : Size)
    (dst other : Reg) (value : Word) (h : dst ≠ other) :
    (state.writeReg size dst value).getReg other = state.getReg other := by
  simp [State.writeReg, h]

@[simp] theorem State.trim_getReg_writeReg (state : State) (size : Size)
    (reg : Reg) (value : Word) :
    size.trim ((state.writeReg size reg value).getReg reg) = size.trim value := by
  rw [State.getReg_writeReg_self]
  split
  · simp [Size.trim, BitVec.and_or_distrib_right, BitVec.and_assoc]
  · exact Size.trim_idempotent size value

theorem State.writeReg_preserves_upper (state : State) (size : Size) (reg : Reg)
    (value : Word) (h : size = .b8 ∨ size = .b16) :
    (state.writeReg size reg value).getReg reg &&& ~~~size.mask =
      state.getReg reg &&& ~~~size.mask := by
  have hp : (size == .b8 || size == .b16) = true := by
    rcases h with rfl | rfl <;> rfl
  simp [State.getReg_writeReg_self, hp, Size.trim,
    BitVec.and_or_distrib_right, BitVec.and_assoc]

@[simp] theorem State.getReg_writeReg_b32 (state : State) (reg : Reg) (value : Word) :
    (state.writeReg .b32 reg value).getReg reg = Size.b32.trim value := by
  rw [State.getReg_writeReg_self]
  rfl

@[simp] theorem State.getReg_writeReg_b64 (state : State) (reg : Reg) (value : Word) :
    (state.writeReg .b64 reg value).getReg reg = value := by
  rw [State.getReg_writeReg_self]
  exact Size.trim_b64 value

@[simp] theorem State.writeReg_rip (state : State) (size : Size) (reg : Reg)
    (value : Word) : (state.writeReg size reg value).rip = state.rip := rfl

@[simp] theorem State.writeReg_flags (state : State) (size : Size) (reg : Reg)
    (value : Word) : (state.writeReg size reg value).flags = state.flags := rfl

@[simp] theorem State.writeReg_memory (state : State) (size : Size) (reg : Reg)
    (value : Word) : (state.writeReg size reg value).memory = state.memory := rfl

@[simp] theorem arithmetic_trim (size : Size) (subtract : Bool) (a b : Word)
    (carry : Bool) :
    size.trim (arithmetic size subtract a b carry).1 =
      (arithmetic size subtract a b carry).1 :=
  Size.trim_idempotent size _

/-- The low word of ADD/ADC is the mathematical sum modulo the operand width. -/
theorem arithmetic_add_toNat (size : Size) (a b : Word) (carry : Bool) :
    (arithmetic size false a b carry).1.toNat =
      ((size.trim a).toNat + (size.trim b).toNat + (if carry then 1 else 0)) %
        2 ^ size.bits := by
  have hd : 2 ^ size.bits ∣ 2 ^ 64 := by cases size <;> decide
  change (size.trim (a + b + BitVec.ofNat 64 (if carry then 1 else 0))).toNat = _
  rw [Size.trim_toNat, BitVec.toNat_add, Nat.mod_mod_of_dvd _ hd]
  cases carry <;>
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Size.trim_toNat, Nat.add_mod,
      Nat.mod_mod_of_dvd _ hd]

theorem arithmetic_add_cf (size : Size) (a b : Word) (carry : Bool) :
    (arithmetic size false a b carry).2.cf =
      some (decide (2 ^ size.bits ≤
        (size.trim a).toNat + (size.trim b).toNat + (if carry then 1 else 0))) := rfl

/-- The result and CF together retain the full unsigned sum, including carry-in. -/
theorem arithmetic_add_conservation (size : Size) (a b : Word) (carry : Bool) :
    (arithmetic size false a b carry).1.toNat +
        (if (arithmetic size false a b carry).2.cf = some true then 2 ^ size.bits else 0) =
      (size.trim a).toNat + (size.trim b).toNat + (if carry then 1 else 0) := by
  rw [arithmetic_add_toNat, arithmetic_add_cf]
  simp only [Option.some.injEq, decide_eq_true_eq]
  have ha := size.trim_lt a
  have hb := size.trim_lt b
  have hc : (if carry then 1 else 0 : Nat) ≤ 1 := by cases carry <;> decide
  by_cases h : 2 ^ size.bits ≤
      (size.trim a).toNat + (size.trim b).toNat + (if carry then 1 else 0)
  · rw [if_pos h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]
    omega

/-- A register ADD reads no incoming flags. The length premise isolates encoding. -/
theorem execInstr_add_reg (size : Size) (dst src : Reg) (state : State) (length : Nat)
    (hsize : (Instr.alu .add size dst (.reg src)).byteSize = .ok length) :
    execInstr (.alu .add size dst (.reg src)) state =
      let result := arithmetic size false (state.getReg dst) (size.trim (state.getReg src)) false
      .ok { state.writeReg size dst result.1 with
        rip := state.rip + BitVec.ofNat 64 length, flags := result.2 } := by
  unfold execInstr
  rw [hsize]
  rfl

/-- A register ADC reads CF before updating the destination, even when dst = src. -/
theorem execInstr_adc_reg (size : Size) (dst src : Reg) (state : State) (length : Nat)
    (hsize : (Instr.alu .adc size dst (.reg src)).byteSize = .ok length) :
    execInstr (.alu .adc size dst (.reg src)) state = (do
      let carry ← requireFlag state.flags.cf
      let result := arithmetic size false (state.getReg dst) (size.trim (state.getReg src)) carry
      pure { state.writeReg size dst result.1 with
        rip := state.rip + BitVec.ofNat 64 length, flags := result.2 }) := by
  unfold execInstr
  rw [hsize]
  rfl

theorem execInstr_adc_reg_of_cf (size : Size) (dst src : Reg) (state : State)
    (length : Nat) (carry : Bool)
    (hsize : (Instr.alu .adc size dst (.reg src)).byteSize = .ok length)
    (hcf : state.flags.cf = some carry) :
    execInstr (.alu .adc size dst (.reg src)) state =
      let result := arithmetic size false (state.getReg dst) (size.trim (state.getReg src)) carry
      .ok { state.writeReg size dst result.1 with
        rip := state.rip + BitVec.ofNat 64 length, flags := result.2 } := by
  rw [execInstr_adc_reg size dst src state length hsize, hcf]
  rfl

theorem execInstr_adc_reg_undefined_cf (size : Size) (dst src : Reg) (state : State)
    (length : Nat) (hsize : (Instr.alu .adc size dst (.reg src)).byteSize = .ok length)
    (hcf : state.flags.cf = none) :
    execInstr (.alu .adc size dst (.reg src)) state = .error .undefinedFlag := by
  rw [execInstr_adc_reg size dst src state length hsize, hcf]
  rfl

/-- Instruction-level conservation, with subregister preservation handled by writeReg. -/
theorem execInstr_add_reg_conservation (size : Size) (dst src : Reg) (state : State)
    (length : Nat) (hsize : (Instr.alu .add size dst (.reg src)).byteSize = .ok length) :
    (execInstr (.alu .add size dst (.reg src)) state).map (fun next =>
      (size.trim (next.getReg dst)).toNat +
        (if next.flags.cf = some true then 2 ^ size.bits else 0)) =
      .ok ((size.trim (state.getReg dst)).toNat + (size.trim (state.getReg src)).toNat) := by
  rw [execInstr_add_reg size dst src state length hsize]
  change Except.ok ((size.trim ((state.writeReg size dst _).getReg dst)).toNat + _) = _
  rw [State.trim_getReg_writeReg, arithmetic_trim]
  congr 1
  simpa only [Size.trim_idempotent, Bool.false_eq_true, if_false, Nat.add_zero] using
    arithmetic_add_conservation size (state.getReg dst) (size.trim (state.getReg src)) false

theorem execInstr_adc_reg_conservation (size : Size) (dst src : Reg) (state : State)
    (length : Nat) (carry : Bool)
    (hsize : (Instr.alu .adc size dst (.reg src)).byteSize = .ok length)
    (hcf : state.flags.cf = some carry) :
    (execInstr (.alu .adc size dst (.reg src)) state).map (fun next =>
      (size.trim (next.getReg dst)).toNat +
        (if next.flags.cf = some true then 2 ^ size.bits else 0)) =
      .ok ((size.trim (state.getReg dst)).toNat + (size.trim (state.getReg src)).toNat +
        (if carry then 1 else 0)) := by
  rw [execInstr_adc_reg_of_cf size dst src state length carry hsize hcf]
  change Except.ok ((size.trim ((state.writeReg size dst _).getReg dst)).toNat + _) = _
  rw [State.trim_getReg_writeReg, arithmetic_trim]
  congr 1
  simpa only [Size.trim_idempotent] using
    arithmetic_add_conservation size (state.getReg dst) (size.trim (state.getReg src)) carry

end LeanAsm.X64
