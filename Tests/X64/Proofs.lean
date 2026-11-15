import LeanAsm

open LeanAsm.X64

-- should preserve every other register when a partial register is written
example (state : State) (dst other : Reg) (value : Word) (h : dst ≠ other) :
    (state.writeReg .b8 dst value).getReg other = state.getReg other := by
  exact State.getReg_writeReg_of_ne state .b8 dst other value h

-- should preserve upper bits when writing a byte
example (state : State) (dst : Reg) (value : Word) :
    (state.writeReg .b8 dst value).getReg dst &&& ~~~Size.b8.mask =
      state.getReg dst &&& ~~~Size.b8.mask := by
  exact State.writeReg_preserves_upper state .b8 dst value (by simp)

-- should replace the whole register when writing a qword
example (state : State) (dst : Reg) (value : Word) :
    (state.writeReg .b64 dst value).getReg dst = value := by
  simp

-- should retain the entire mathematical sum in the low result and carry
example (size : Size) (a b : Word) (carry : Bool) :
    (arithmetic size false a b carry).1.toNat +
        (if (arithmetic size false a b carry).2.cf = some true then 2 ^ size.bits else 0) =
      (size.trim a).toNat + (size.trim b).toNat + (if carry then 1 else 0) := by
  exact arithmetic_add_conservation size a b carry

-- should read the written low bits at every operand width
example (state : State) (size : Size) (dst : Reg) (value : Word) :
    (size.trim ((state.writeReg size dst value).getReg dst)).toNat =
      value.toNat % 2 ^ size.bits := by
  rw [State.trim_getReg_writeReg, Size.trim_toNat]

-- should preserve upper bits when writing a word
example (state : State) (dst : Reg) (value : Word) :
    (state.writeReg .b16 dst value).getReg dst &&& ~~~Size.b16.mask =
      state.getReg dst &&& ~~~Size.b16.mask := by
  exact State.writeReg_preserves_upper state .b16 dst value (by simp)

-- should clear all upper 32 bits when writing a dword
example (state : State) (dst : Reg) (value : Word) :
    ((state.writeReg .b32 dst value).getReg dst).toNat < 2 ^ 32 := by
  rw [State.getReg_writeReg_b32]
  exact Size.trim_lt .b32 value

-- should leave non-register state unchanged when writing at any width
example (state : State) (size : Size) (dst : Reg) (value : Word) :
    let next := state.writeReg size dst value
    (next.rip, next.flags, next.memory) = (state.rip, state.flags, state.memory) := by
  simp

-- should connect ADD to the full sum even when all incoming flags are undefined
example (state : State) :
    (execInstr (.alu .add .b64 .rax (.reg .r8))
      { state with flags := Flags.undefined }).map (fun next =>
        (next.getReg .rax).toNat + (if next.flags.cf = some true then 2 ^ 64 else 0)) =
      .ok ((state.getReg .rax).toNat + (state.getReg .r8).toNat) := by
  simpa only [Size.trim_b64, Size.bits, State.getReg] using
    execInstr_add_reg_conservation .b64 .rax .r8
      { state with flags := Flags.undefined } 3 (by rfl)

-- should consume the old value once per operand when ADC aliases its destination
example (state : State) (carry : Bool) :
    (execInstr (.alu .adc .b64 .rax (.reg .rax))
      { state with flags := { state.flags with cf := some carry } }).map (fun next =>
        (next.getReg .rax).toNat + (if next.flags.cf = some true then 2 ^ 64 else 0)) =
      .ok ((state.getReg .rax).toNat + (state.getReg .rax).toNat +
        (if carry then 1 else 0)) := by
  simpa only [Size.trim_b64, Size.bits, State.getReg] using
    execInstr_adc_reg_conservation .b64 .rax .rax
      { state with flags := { state.flags with cf := some carry } } 3 carry (by rfl) rfl

-- should trap instead of inventing a carry when ADC reads an undefined CF
example (state : State) :
    execInstr (.alu .adc .b8 .rax (.reg .r8)) { state with flags := Flags.undefined } =
      .error .undefinedFlag := by
  exact execInstr_adc_reg_undefined_cf .b8 .rax .r8
    { state with flags := Flags.undefined } 3 (by rfl) rfl

-- should advance RIP by the encoded length even across address wraparound
example (state : State) :
    (execInstr (.alu .add .b16 .rax (.reg .r8)) state).map (·.rip) =
      .ok (state.rip + 4) := by
  rw [execInstr_add_reg .b16 .rax .r8 state 4 (by rfl)]
  rfl

-- should preserve registers other than the destination when executing byte ADD
example (state : State) :
    (execInstr (.alu .add .b8 .rax (.reg .r8)) state).map (·.getReg .r9) =
      .ok (state.getReg .r9) := by
  rw [execInstr_add_reg .b8 .rax .r8 state 3 (by rfl)]
  change Except.ok ((state.writeReg .b8 .rax _).getReg .r9) = _
  rw [State.getReg_writeReg_of_ne state .b8 .rax .r9 _ (by decide)]

-- should carry out when ADC increments the largest value at every width
example (size : Size) :
    (arithmetic size false size.mask 0 true).1.toNat = 0 ∧
      (arithmetic size false size.mask 0 true).2.cf = some true := by
  rw [arithmetic_add_toNat, arithmetic_add_cf]
  cases size <;> decide

-- should compose low and high limb additions without losing either carry
example (aLo aHi bLo bHi : Word) :
    let low := arithmetic .b64 false aLo bLo false
    let high := arithmetic .b64 false aHi bHi (low.2.cf.getD false)
    low.1.toNat + 2 ^ 64 *
        (high.1.toNat + (if high.2.cf = some true then 2 ^ 64 else 0)) =
      aLo.toNat + bLo.toNat + 2 ^ 64 * (aHi.toNat + bHi.toNat) := by
  dsimp only
  have low := arithmetic_add_conservation .b64 aLo bLo false
  have high := arithmetic_add_conservation .b64 aHi bHi
    ((arithmetic .b64 false aLo bLo false).2.cf.getD false)
  rw [arithmetic_add_cf] at low high ⊢
  simp only [Size.trim_b64, Size.bits, Bool.false_eq_true, if_false, Nat.add_zero] at low high ⊢
  by_cases h : 2 ^ 64 ≤ aLo.toNat + bLo.toNat
  · simp only [h, decide_true, Option.getD_some, if_true] at low high ⊢
    omega
  · simp only [h, decide_false, Option.getD_some, Option.some.injEq, Bool.false_eq_true,
      if_false, Nat.add_zero] at low high ⊢
    omega

/-- info: 'LeanAsm.X64.State.getReg_writeReg_of_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms State.getReg_writeReg_of_ne

/-- info: 'LeanAsm.X64.State.writeReg_preserves_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms State.writeReg_preserves_upper

/-- info: 'LeanAsm.X64.arithmetic_add_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arithmetic_add_conservation

/-- info: 'LeanAsm.X64.execInstr_adc_reg_undefined_cf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms execInstr_adc_reg_undefined_cf

/-- info: 'LeanAsm.X64.execInstr_add_reg_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execInstr_add_reg_conservation

/-- info: 'LeanAsm.X64.execInstr_adc_reg_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms execInstr_adc_reg_conservation
