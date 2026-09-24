//
//  TinyGLLApp.swift
//  tinyGLL
//
//  Created by Johannes Brands on 2026.09.16.
//

import SwiftUI

@main
struct TinyGLLApp: App {

    /// One parse per window group. Held here rather than in ExplorerView so the menu
    /// commands, which live outside the scene's content, can reach it too.
    @State private var model = ParserModel()

    var body: some Scene {
        WindowGroup("tinyGLL") {
            ExplorerView()
                .environment(model)
        }
        .defaultSize(width: 1180, height: 760)
        .commands { ParserCommands(model: model) }
    }
}
