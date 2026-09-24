//
//  extensions.swift
//  tinyGLL
//
//  Created by Johannes Brands on 2026.08.29.
//

import Foundation

nonisolated extension GrammarNode: Hashable {
    static func == (lhs: GrammarNode, rhs: GrammarNode) -> Bool {
        lhs.number == rhs.number
    }
    func hash(into hasher: inout Hasher) {
        hasher.combine(number)
    }
}

nonisolated extension GrammarNode: CustomStringConvertible {
    var description: String { "\(number) \(name)" }
}

nonisolated extension GrammarNode {
    /// The seq/alt link table for this production, one node per line. Used to be printed to
    /// stdout by the CLI's trace mode; it now feeds the explorer's Trace pane, so it returns
    /// the text instead.
    func dump() -> String {
        func line(_ node: GrammarNode) -> String {
            var e = "\(node.number)\t\(node.kind)\t"
            if let s = node.seq { e += "\ts\(s.number)" }
            if let a = node.alt { e += "\ta\(a.number)" }
            return e + "\n"
        }

        var text = ""
        var node: GrammarNode? = self
        while let current = node {
            text += line(current)
            if current.kind == .N && current.seq == nil {
                node = current.alt
            } else if current.kind == .END {
                node = current.alt?.alt
            } else {
                node = current.seq
            }
        }
        return text
    }
}

nonisolated extension ParsePosition: Comparable, CustomStringConvertible {
    static func < (lhs: ParsePosition, rhs: ParsePosition) -> Bool {
        lhs.description < rhs.description
    }
    var description: String { "\(slot).\(index)" }
}

nonisolated extension ParseCluster: CustomStringConvertible {
    // The cluster's (X, k) identity lives in its crf key, so only the contents print here.
    var description: String { "returns \(returns.sorted()) pops \(pops.sorted())" }
}

nonisolated extension BinarySpan: Comparable, CustomStringConvertible {
    var description: String { "\(i):\(k):\(j)" }

    static func < (lhs: BinarySpan, rhs: BinarySpan) -> Bool {
        if lhs.i != rhs.i { return lhs.i < rhs.i }
        if lhs.k != rhs.k { return lhs.k < rhs.k }
        return lhs.j < rhs.j
    }
}
