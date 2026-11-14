import LeanAsm.X64.Basic

namespace LeanAsm.X64

structure Region where
  base : Word
  bytes : Array UInt8
  writable : Bool
  deriving Repr

def Region.endAddr (region : Region) : Nat := region.base.toNat + region.bytes.size

def Region.contains (region : Region) (width : Nat) (address : Word) : Bool :=
  decide (region.base.toNat ≤ address.toNat ∧ width ≤ region.bytes.size ∧
    address.toNat - region.base.toNat ≤ region.bytes.size - width)

def Region.disjoint (a b : Region) : Bool :=
  decide (a.endAddr ≤ b.base.toNat ∨ b.endAddr ≤ a.base.toNat)

structure Memory where
  regions : Array Region := #[]
  deriving Repr

def Memory.valid (memory : Memory) : Bool :=
  memory.regions.all (fun r => decide (0 < r.bytes.size ∧ r.endAddr ≤ 2 ^ 64)) &&
    decide (memory.regions.toList.Pairwise (fun a b => a.disjoint b = true))

/-- Ordinary scalar accesses may be unaligned. A complete access must fit in one
    region; this model has no MMU, segmentation, or alignment-check mode. -/
def Memory.locate (memory : Memory) (size : Size) (address : Word) :
    Except Error (Nat × Nat) := do
  unless memory.valid do throw .invalidMemory
  match memory.regions.findIdx? (fun r => r.contains size.bytes address) with
  | none => throw .memoryBounds
  | some index =>
      if h : index < memory.regions.size then
        return (index, address.toNat - memory.regions[index].base.toNat)
      else throw .memoryBounds

def Memory.load (memory : Memory) (size : Size) (address : Word) : Except Error Word := do
  let (index, offset) ← memory.locate size address
  if h : index < memory.regions.size then
    let bytes := memory.regions[index].bytes
    (List.range size.bytes).foldlM (fun value i =>
      if h : offset + i < bytes.size then
        return value ||| (BitVec.ofNat 64 bytes[offset + i].toNat <<< (8 * i))
      else throw .memoryBounds) 0
  else throw .memoryBounds

def Memory.store (memory : Memory) (size : Size) (address value : Word) :
    Except Error Memory := do
  let (index, offset) ← memory.locate size address
  if h : index < memory.regions.size then
    let region := memory.regions[index]
    unless region.writable do throw .readOnlyMemory
    let bytes ← (List.range size.bytes).foldlM (fun bytes i =>
      if h : offset + i < bytes.size then
        return bytes.set (offset + i) ((value >>> (8 * i)).toNat.toUInt8)
      else throw .memoryBounds) region.bytes
    return { regions := memory.regions.set index { region with bytes := bytes } }
  else throw .memoryBounds

end LeanAsm.X64
