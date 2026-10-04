# Active TODO

This file is the canonical active TODO list for the project.
It holds actionable items only.
Put completed work and historical explanations in design notes or commit messages.

1. Accept escaped macro names such as `#\`expect\`(...)`. The crawl rejects
    apple/swift-testing's `#\`expect\`(Bool(true))`, expecting `::` after the escaped identifier.
    `macroHead` uses `poundName` plus exclusions and a module-selector form; it likely needs an
    escaped-identifier macro-head path rather than treating `#` + escaped identifier as a module
    selector start.

2. Accept escaped bare ObjC selector names in `@objc(...)`. The crawl rejects
    `@objc(\`testExplicitNameWithBackticks\`)` in apple/swift-testing. `objcSelector = identifier`
    covers bare unescaped names, and `objcSelectorPiece = identifier? ":"` covers colon pieces; add
    the escaped bare-name case without broadening selector pieces more than SwiftSyntax does.

3. Reduce and fix the remaining close-brace/EOF underaccepts from the 2026-10-03 crawl. Seven
    compiler-accepted files fail only when the parse finally reaches a closing brace or EOF
    (OpenEmu FileManager+Hashing.swift, FluidVoice AutomaticDictionaryTrainingSession.swift and
    PronunciationDictionaryStore.swift, swift-distributed-actors
    AggressiveNodeReplacementClusteredTests.swift, CopilotForXcode GitHubCopilotModelPicker.swift
    and SuggestionSettingsGeneralSectionView.swift, alt-tab-macos TestReducerRunner.swift). The
    final token is not enough to identify the root cause; reduce each file or bisect declarations,
    then split this TODO into concrete grammar issues before editing `Swift.apus`.

