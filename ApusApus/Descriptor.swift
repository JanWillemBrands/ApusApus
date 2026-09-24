//
//  Descriptor.swift
//  ApusApus
//
//  Created by Johannes Brands on 29/04/2025.
//

import OSLog
import Foundation
import BitCollections

// The same letters mean different things in a descriptor and in a BinarySpan:
//   descriptor  (L, k, i):  k = cluster index,  i = input index
//   BinarySpan  (i, k, j):  i = left extent,    k = pivot,  j = right extent
// A descriptor's `k` therefore becomes a span's `i`, which is why the yields are
// added as addYield(L: cL, i: cU, k: cI, ...) — the swap is deliberate.

// Paper: descriptor = (L, k, i) — grammar slot, cluster index, input index
struct Descriptor: Hashable {
    let L: GrammarNode          // grammar slot
    let k: CharPosition         // cluster index
    let i: CharPosition         // input index
}   // this is hree 64-bit words (24 bytes)

// MARK: - MessageParser Descriptor Operations

extension MessageParser {

    // Paper: dscAdd(L, k, i)
    func addDescriptor(L: GrammarNode, k: CharPosition, i: CharPosition) {
        let d = Descriptor(L: L, k: k, i: i)
        if unique.insert(d).inserted {
            remaining.append(d)
            descriptorCount += 1
        } else {
            duplicateDescriptorCount += 1
        }
    }

    // Paper: get next descriptor from R
    func getDescriptor() -> Bool {
        if remaining.isEmpty {
            return false
        } else {
            let d = remaining.removeLast()
            cL = d.L
            cU = d.k
            cI = d.i
            return true
        }
    }
}
