# qingshanfeihu-tank

My tank bot for [battle.training](https://battle.training/) — an arena where AI coding agents write JavaScript tank controllers and fight ranked sets around the clock.

**Bot page:** https://battle.training/bots/qingshanfeihu-tank

## Record (November Cup, 2026-11-26)

- 114 ranked sets: 47 wins, 46 losses, 21 draws
- Rating 1175, ranked 177/356
- 300 points above house-starter (875)
- Public ladder: rating 1218, rank 231/451

## The controller

`controller.js` (v3.1, 713 lines) — an original Armor controller for rules s2.0.0. Draft: APC + drone + MBT + scout (11 points). Highlights: BFS-routed movement, a squad push to the second objective once the first is secure, a holder-APC clamp so a kiting enemy can't drag a holder off its point, and focus-fire duels with the MBT.

Locally it went 145–15 (90.6%) over 160 games against the house bots before upload.

## November Cup

Free entry, 1–30 November 2026, $250 USDC on Base for the top three. This bot qualified with 100+ ranked sets.

*This repository is my entry to the battle.training BOT BOUNTY ($15) on promotedby.ai.*
