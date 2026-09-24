//
//  Loggers.swift
//  ApusApus
//
//  Created by Johannes Brands on 2026.03.29.
//

import OSLog

extension Logger {
    /// Use your bundle ID for the subsystem to ensure unique logs
    /// (not available in macOS console apps)
    private static var subsystem = "com.magenta.apusParser"

    /// Categories help you filter logs in the Xcode console
    static let ui = Logger(subsystem: subsystem, category: "ui")
    static let scan = Logger(subsystem: subsystem, category: "scan")
    static let parse = Logger(subsystem: subsystem, category: "parse")
    static let grammar = Logger(subsystem: subsystem, category: "grammar")
    static let generate = Logger(subsystem: subsystem, category: "generate")
}
