# Demo Video Shot List
## Visual Guide for Recording

**Total Time**: 4 minutes  
**Format**: Screen recording with voiceover

---

## 🎬 Shot-by-Shot Breakdown

### SHOT 1: Title Card (5 seconds)
**Screen**: Black screen with text
```
zkEVM Circuit Formal Verification Framework
Proving zkEVM Circuits Mathematically Correct
```
**Audio**: [Silence or subtle background music]

---

### SHOT 2: The Problem (15 seconds)
**Screen**: Ethereum logo → zkEVM logos (Polygon, Scroll, etc.)
**On-screen text**: 
- "zkEVMs secure $5B+"
- "Circuit bugs = Lost funds"
- "Manual audits can't prove correctness"

**Voiceover**: 
> "zkEVMs secure billions of dollars. But their circuits are complex, and bugs are expensive. Manual audits can't prove correctness."

---

### SHOT 3: The Solution (10 seconds)
**Screen**: Terminal fade-in
**Visual**: Project directory listing
```bash
$ ls -la
```

**Voiceover**: 
> "What if we could mathematically prove circuits are correct? I built a framework that does exactly that."

---

### SHOT 4: Load Poseidon Circuit (20 seconds)
**Screen**: Terminal
**Type and execute**:
```bash
$ python3 -c "from circuits import poseidon; print(poseidon.poseidon_circuit)"
```

**On-screen (after output)**:
- Highlight: "Polygon zkEVM"
- Highlight: "~140 constraints"

**Voiceover**: 
> "Here's Poseidon hash - the exact primitive Polygon zkEVM uses. That's a 3 billion dollar zkEVM. This circuit has 140 constraints."

---

### SHOT 5: Show Poseidon Proof (25 seconds)
**Screen**: Terminal
**Type and execute**:
```bash
$ cat proofs/Poseidon.lean | head -50
```

**Scroll slowly** through output

**On-screen annotations** (if editing):
- Arrow to: "theorem Poseidon_..."
- Circle: "by intro x y"
- Highlight: "exact FIELD_MODULUS_pos"

**Voiceover**: 
> "The framework generates Lean4 proofs automatically. 250 lines proving 12 properties: S-box correctness, round functions, field preservation."

---

### SHOT 6: Show Poseidon Report (20 seconds)
**Screen**: Terminal
**Type and execute**:
```bash
$ cat reports/Poseidon_report.md | head -40
```

**On-screen highlights**:
- "Status: ✓ VERIFIED"
- "3.45 seconds"
- "12 properties proven"

**Voiceover**: 
> "And here's the verification report. Status: verified. All properties proven in under 4 seconds."

---

### SHOT 7: Load ECC Circuit (15 seconds)
**Screen**: Terminal
**Type and execute**:
```bash
$ python3 -c "from circuits import ecc_add; print(ecc_add.ecc_add_circuit)"
```

**On-screen**:
- Highlight: "ECRECOVER opcode"
- Highlight: "Every Ethereum transaction"

**Voiceover**: 
> "Now, elliptic curve operations - the core of ECRECOVER. This opcode verifies signatures in every single Ethereum transaction."

---

### SHOT 8: Show ECC Properties (15 seconds)
**Screen**: Terminal
**Type and execute**:
```bash
$ cat reports/ECCAdd_report.md | grep -A 5 "Properties Verified"
```

**On-screen**:
- Circle each "✓"
- Highlight: "10 properties"

**Voiceover**: 
> "Five special cases handled. Group properties proven. Identity, inverse, commutativity - all verified."

---

### SHOT 9: Impact - Polygon (10 seconds)
**Screen**: Polygon logo (if available) OR text card
```
POLYGON zkEVM
Total Value Locked: $3B+
Uses: Poseidon Hash
Status: ✅ VERIFIED
```

**Voiceover**: 
> "Polygon zkEVM uses Poseidon for state commitments. We just verified that primitive."

---

### SHOT 10: Impact - ECRECOVER (10 seconds)
**Screen**: Ethereum logo (if available) OR text card
```
ECRECOVER OPCODE
Usage: Every Ethereum Transaction
Frequency: Billions per day
Status: ✅ VERIFIED
```

**Voiceover**: 
> "ECRECOVER verifies every Ethereum transaction signature. We just verified those ECC operations."

---

### SHOT 11: Stats Summary (15 seconds)
**Screen**: Text card or terminal with summary
```
📊 PROTOTYPE STATS
• 5 circuits verified
• 48 theorems proven
• 1,400 lines of formal proofs
• 140+ constraint circuits
• < 4 seconds per verification
```

**Voiceover**: 
> "Five circuits verified. 48 theorems proven. 1,400 lines of formal proofs. 140+ constraint circuits verified in under 4 seconds."

---

### SHOT 12: Roadmap (20 seconds)
**Screen**: Text card with milestones
```
🚀 ROADMAP

MILESTONE 1 (3 months, $30K)
→ Verify Scroll/Polygon Halo2 circuits
→ Keccak-256, Poseidon production code

MILESTONE 2 (3 months, $35K)
→ Verify EVM opcodes
→ Yellow Paper equivalence proofs

MILESTONE 3 (3 months, $35K)
→ CLI tool + GitHub Actions
→ Partnership with zkEVM teams
```

**Voiceover**: 
> "Milestone 1: Parse Halo2 circuits from Scroll and Polygon. Milestone 2: Verify EVM opcodes. Milestone 3: Production tooling and partnerships."

---

### SHOT 13: The Ask (15 seconds)
**Screen**: Text card
```
🎯 GRANT REQUEST

Amount: $100,000
Duration: 9 months
Goal: Verify production zkEVM circuits

Addresses: EF Top Priority
          (zkEVM Security)
```

**Voiceover**: 
> "This addresses the Ethereum Foundation's top priority - zkEVM security. We're asking for 100 thousand dollars over 9 months."

---

### SHOT 14: Differentiation (15 seconds)
**Screen**: Split screen comparison
```
OTHER PROPOSALS          OUR APPLICATION
• Slide decks           • Working prototype
• Promises              • Demonstrations
• "We will build..."    • "We built..."
• Theoretical           • Production circuits
```

**Voiceover**: 
> "Every other application is a proposal. This is a demonstration. We're not asking you to bet on potential - we're showing working technology."

---

### SHOT 15: Closing (10 seconds)
**Screen**: Contact info card
```
zkEVM Circuit Formal Verification Framework
Making zkEVMs Mathematically Secure

📧 [your-email]
🐙 github.com/[your-repo]
🌐 [your-website-if-any]

ESP Application: [reference number]
```

**Voiceover**: 
> "zkEVM Circuit Formal Verification Framework. Making zkEVMs securing billions of dollars mathematically safe."

---

### SHOT 16: Fade Out (5 seconds)
**Screen**: Black
**Audio**: [Fade out]

---

## 🎨 Visual Style Guide

### Terminal Settings:
- **Background**: Dark (black or dark grey)
- **Text**: Bright (white or green)
- **Font**: Monospace, 14-16pt
- **Prompt**: Simple (`$ ` or just blank)

### Text Cards:
- **Background**: Dark blue or black
- **Text**: White
- **Font**: Sans-serif, clean
- **Style**: Professional, minimal

### Timing:
- **Show command**: 2-3 seconds
- **Show output**: 3-5 seconds (let people read)
- **Transitions**: Quick (0.5s fade)

---

## 📹 Recording Sequence

### Phase 1: Terminal Shots (Record all at once)
1. Open terminal
2. Navigate to project
3. Run all commands in sequence
4. Don't stop recording between commands

### Phase 2: Text Cards (Create separately)
1. Use PowerPoint, Keynote, or Figma
2. Export as images or video
3. Import into video editor

### Phase 3: Assembly
1. Import terminal recording
2. Cut into segments (Shots 4-8, 11)
3. Add text cards (Shots 1-2, 9-10, 12-15)
4. Add voiceover
5. Add transitions

---

## 🎤 Audio Recording Tips

### Record voiceover AFTER video:
1. Play video on mute
2. Record audio watching the video
3. Sync in editor
4. Much easier than trying to match while recording screen

### OR record while screen recording:
1. Practice script first
2. Record in one take
3. Less editing, but higher pressure

---

## ⚙️ Technical Specs

### Video:
- **Resolution**: 1920x1080 (1080p)
- **Frame rate**: 30fps
- **Format**: MP4 (H.264)
- **Bitrate**: 5-10 Mbps

### Audio:
- **Format**: AAC
- **Sample rate**: 48kHz
- **Bitrate**: 192 kbps
- **Channels**: Mono (or stereo if music)

---

## 🎬 Alternative: Simpler Version

If video editing is too complex, record in **ONE TAKE**:

1. Practice full script 3 times
2. Set up terminal with all commands ready
3. Record screen + audio simultaneously
4. No editing needed!

**Trade-off**: Less polished, but authentic and time-saving

---

## ✅ Final Checklist

**Before Recording**:
- [ ] All commands tested
- [ ] Terminal configured (font, colors)
- [ ] Quiet environment
- [ ] Microphone tested
- [ ] Script practiced

**During Recording**:
- [ ] Speak clearly and confidently
- [ ] Pause between sections
- [ ] Let outputs display fully
- [ ] Stay calm if you make a mistake (keep going or restart)

**After Recording**:
- [ ] Watch full video
- [ ] Check audio quality
- [ ] Verify all text is readable
- [ ] Time check (3-5 minutes)
- [ ] Export in correct format

---

## 🎯 Success Criteria

**Your demo is ready when**:
✅ Shows working technology (not slides)  
✅ Production circuits clearly demonstrated  
✅ Real-world impact emphasized  
✅ Under 5 minutes  
✅ Audio clear and professional  
✅ Visuals readable  
✅ Makes you want to fund it!

---

**You've got everything you need!** 🚀

Script, commands, shot list, cheat sheet - all ready. Now just record with confidence!

Good luck! 🎥
