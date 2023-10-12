// Goal of this file:
//   Curently, Gobra's support for resoning about the values of bitwise operations is very limited.
//   While this is not addressed, we rely on Dafny to prove that the lemmas hold, and we just provide
//   an axiomatized version of the Lemma in Gobra. This is sub-optimal, but it is less than nothing.

// How to extend:
//   When a new lemma is needed, we should prove it in this file. If the lemma
//   applies to Go's int type, we should introduce a lemma for when int has 32bit
//   and for when it has 64bit.

lemma ByteValue(b: bv8)
    ensures 0 <= (b as int) && (b as int) < 256
{}

lemma BitAnd3_32bit(b: bv32)
    ensures var res := b & 0x3;
        0 <= res && res <= 3  &&
        (b == 0 ==> res == 0) &&
        (b == 3 ==> res == 3) &&
        (b == 4 ==> res == 0)
{}

lemma BitAnd3_64bit(b: bv64)
    ensures var res := b & 0x3;
        0 <= res <= 3  &&
        (b == 0 ==> res == 0) &&
        (b == 3 ==> res == 3) &&
        (b == 4 ==> res == 0)
{}

lemma BitAnd7_32bit(b: bv32)
    ensures var res := b & 0x7;
        0 <= res <= 7
{}

lemma BitAnd7_64bit(b: bv64)
    ensures var res := b & 0x7;
        0 <= res <= 7
{}

lemma Shift30LessThan4(b: bv32)
    ensures var res := b >> 30;
        0 <= res <= 3
{}

lemma And3fAtMost64(b: bv8)
    ensures var res := b & 0x3F;
        0 <= res < 64
{}