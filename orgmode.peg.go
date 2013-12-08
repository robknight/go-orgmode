package orgmode

import (
	/*"bytes"*/
	"fmt"
	"math"
	"sort"
	"strconv"
)

const END_SYMBOL rune = 4

/* The rule types inferred from the grammar are below. */
type Rule uint8

const (
	RuleUnknown Rule = iota
	RuleStart
	RuleMarkup
	RuleHeadline
	RuleOrgNode
	RuleContentLine
	RuleContent
	RuleHeadlineText
	RuleStars
	RulePropertiesBegin
	RulePropertiesEnd
	RuleProperties
	RulePropertyPair
	RulePropertyKeyChar
	RulePropertyKey
	RulePropertyValue
	RuleIdentifierChar
	Rule_
	Rule__
	RuleLineEnd
	RuleWhiteSpace
	RuleEOF
	RulePegText

	RulePre_
	Rule_In_
	Rule_Suf
)

var Rul3s = [...]string{
	"Unknown",
	"Start",
	"Markup",
	"Headline",
	"OrgNode",
	"ContentLine",
	"Content",
	"HeadlineText",
	"Stars",
	"PropertiesBegin",
	"PropertiesEnd",
	"Properties",
	"PropertyPair",
	"PropertyKeyChar",
	"PropertyKey",
	"PropertyValue",
	"IdentifierChar",
	"_",
	"__",
	"LineEnd",
	"WhiteSpace",
	"EOF",
	"PegText",

	"Pre_",
	"_In_",
	"_Suf",
}

type TokenTree interface {
	Print()
	PrintSyntax()
	PrintSyntaxTree(buffer string)
	Add(rule Rule, begin, end, next, depth int)
	Expand(index int) TokenTree
	Tokens() <-chan token32
	Error() []token32
	trim(length int)
}

/* ${@} bit structure for abstract syntax tree */
type token16 struct {
	Rule
	begin, end, next int16
}

func (t *token16) isZero() bool {
	return t.Rule == RuleUnknown && t.begin == 0 && t.end == 0 && t.next == 0
}

func (t *token16) isParentOf(u token16) bool {
	return t.begin <= u.begin && t.end >= u.end && t.next > u.next
}

func (t *token16) GetToken32() token32 {
	return token32{Rule: t.Rule, begin: int32(t.begin), end: int32(t.end), next: int32(t.next)}
}

func (t *token16) String() string {
	return fmt.Sprintf("\x1B[34m%v\x1B[m %v %v %v", Rul3s[t.Rule], t.begin, t.end, t.next)
}

type tokens16 struct {
	tree    []token16
	ordered [][]token16
}

func (t *tokens16) trim(length int) {
	t.tree = t.tree[0:length]
}

func (t *tokens16) Print() {
	for _, token := range t.tree {
		fmt.Println(token.String())
	}
}

func (t *tokens16) Order() [][]token16 {
	if t.ordered != nil {
		return t.ordered
	}

	depths := make([]int16, 1, math.MaxInt16)
	for i, token := range t.tree {
		if token.Rule == RuleUnknown {
			t.tree = t.tree[:i]
			break
		}
		depth := int(token.next)
		if length := len(depths); depth >= length {
			depths = depths[:depth+1]
		}
		depths[depth]++
	}
	depths = append(depths, 0)

	ordered, pool := make([][]token16, len(depths)), make([]token16, len(t.tree)+len(depths))
	for i, depth := range depths {
		depth++
		ordered[i], pool, depths[i] = pool[:depth], pool[depth:], 0
	}

	for i, token := range t.tree {
		depth := token.next
		token.next = int16(i)
		ordered[depth][depths[depth]] = token
		depths[depth]++
	}
	t.ordered = ordered
	return ordered
}

type State16 struct {
	token16
	depths []int16
	leaf   bool
}

func (t *tokens16) PreOrder() (<-chan State16, [][]token16) {
	s, ordered := make(chan State16, 6), t.Order()
	go func() {
		var states [8]State16
		for i, _ := range states {
			states[i].depths = make([]int16, len(ordered))
		}
		depths, state, depth := make([]int16, len(ordered)), 0, 1
		write := func(t token16, leaf bool) {
			S := states[state]
			state, S.Rule, S.begin, S.end, S.next, S.leaf = (state+1)%8, t.Rule, t.begin, t.end, int16(depth), leaf
			copy(S.depths, depths)
			s <- S
		}

		states[state].token16 = ordered[0][0]
		depths[0]++
		state++
		a, b := ordered[depth-1][depths[depth-1]-1], ordered[depth][depths[depth]]
	depthFirstSearch:
		for {
			for {
				if i := depths[depth]; i > 0 {
					if c, j := ordered[depth][i-1], depths[depth-1]; a.isParentOf(c) &&
						(j < 2 || !ordered[depth-1][j-2].isParentOf(c)) {
						if c.end != b.begin {
							write(token16{Rule: Rule_In_, begin: c.end, end: b.begin}, true)
						}
						break
					}
				}

				if a.begin < b.begin {
					write(token16{Rule: RulePre_, begin: a.begin, end: b.begin}, true)
				}
				break
			}

			next := depth + 1
			if c := ordered[next][depths[next]]; c.Rule != RuleUnknown && b.isParentOf(c) {
				write(b, false)
				depths[depth]++
				depth, a, b = next, b, c
				continue
			}

			write(b, true)
			depths[depth]++
			c, parent := ordered[depth][depths[depth]], true
			for {
				if c.Rule != RuleUnknown && a.isParentOf(c) {
					b = c
					continue depthFirstSearch
				} else if parent && b.end != a.end {
					write(token16{Rule: Rule_Suf, begin: b.end, end: a.end}, true)
				}

				depth--
				if depth > 0 {
					a, b, c = ordered[depth-1][depths[depth-1]-1], a, ordered[depth][depths[depth]]
					parent = a.isParentOf(b)
					continue
				}

				break depthFirstSearch
			}
		}

		close(s)
	}()
	return s, ordered
}

func (t *tokens16) PrintSyntax() {
	tokens, ordered := t.PreOrder()
	max := -1
	for token := range tokens {
		if !token.leaf {
			fmt.Printf("%v", token.begin)
			for i, leaf, depths := 0, int(token.next), token.depths; i < leaf; i++ {
				fmt.Printf(" \x1B[36m%v\x1B[m", Rul3s[ordered[i][depths[i]-1].Rule])
			}
			fmt.Printf(" \x1B[36m%v\x1B[m\n", Rul3s[token.Rule])
		} else if token.begin == token.end {
			fmt.Printf("%v", token.begin)
			for i, leaf, depths := 0, int(token.next), token.depths; i < leaf; i++ {
				fmt.Printf(" \x1B[31m%v\x1B[m", Rul3s[ordered[i][depths[i]-1].Rule])
			}
			fmt.Printf(" \x1B[31m%v\x1B[m\n", Rul3s[token.Rule])
		} else {
			for c, end := token.begin, token.end; c < end; c++ {
				if i := int(c); max+1 < i {
					for j := max; j < i; j++ {
						fmt.Printf("skip %v %v\n", j, token.String())
					}
					max = i
				} else if i := int(c); i <= max {
					for j := i; j <= max; j++ {
						fmt.Printf("dupe %v %v\n", j, token.String())
					}
				} else {
					max = int(c)
				}
				fmt.Printf("%v", c)
				for i, leaf, depths := 0, int(token.next), token.depths; i < leaf; i++ {
					fmt.Printf(" \x1B[34m%v\x1B[m", Rul3s[ordered[i][depths[i]-1].Rule])
				}
				fmt.Printf(" \x1B[34m%v\x1B[m\n", Rul3s[token.Rule])
			}
			fmt.Printf("\n")
		}
	}
}

func (t *tokens16) PrintSyntaxTree(buffer string) {
	tokens, _ := t.PreOrder()
	for token := range tokens {
		for c := 0; c < int(token.next); c++ {
			fmt.Printf(" ")
		}
		fmt.Printf("\x1B[34m%v\x1B[m %v\n", Rul3s[token.Rule], strconv.Quote(buffer[token.begin:token.end]))
	}
}

func (t *tokens16) Add(rule Rule, begin, end, depth, index int) {
	t.tree[index] = token16{Rule: rule, begin: int16(begin), end: int16(end), next: int16(depth)}
}

func (t *tokens16) Tokens() <-chan token32 {
	s := make(chan token32, 16)
	go func() {
		for _, v := range t.tree {
			s <- v.GetToken32()
		}
		close(s)
	}()
	return s
}

func (t *tokens16) Error() []token32 {
	ordered := t.Order()
	length := len(ordered)
	tokens, length := make([]token32, length), length-1
	for i, _ := range tokens {
		o := ordered[length-i]
		if len(o) > 1 {
			tokens[i] = o[len(o)-2].GetToken32()
		}
	}
	return tokens
}

/* ${@} bit structure for abstract syntax tree */
type token32 struct {
	Rule
	begin, end, next int32
}

func (t *token32) isZero() bool {
	return t.Rule == RuleUnknown && t.begin == 0 && t.end == 0 && t.next == 0
}

func (t *token32) isParentOf(u token32) bool {
	return t.begin <= u.begin && t.end >= u.end && t.next > u.next
}

func (t *token32) GetToken32() token32 {
	return token32{Rule: t.Rule, begin: int32(t.begin), end: int32(t.end), next: int32(t.next)}
}

func (t *token32) String() string {
	return fmt.Sprintf("\x1B[34m%v\x1B[m %v %v %v", Rul3s[t.Rule], t.begin, t.end, t.next)
}

type tokens32 struct {
	tree    []token32
	ordered [][]token32
}

func (t *tokens32) trim(length int) {
	t.tree = t.tree[0:length]
}

func (t *tokens32) Print() {
	for _, token := range t.tree {
		fmt.Println(token.String())
	}
}

func (t *tokens32) Order() [][]token32 {
	if t.ordered != nil {
		return t.ordered
	}

	depths := make([]int32, 1, math.MaxInt16)
	for i, token := range t.tree {
		if token.Rule == RuleUnknown {
			t.tree = t.tree[:i]
			break
		}
		depth := int(token.next)
		if length := len(depths); depth >= length {
			depths = depths[:depth+1]
		}
		depths[depth]++
	}
	depths = append(depths, 0)

	ordered, pool := make([][]token32, len(depths)), make([]token32, len(t.tree)+len(depths))
	for i, depth := range depths {
		depth++
		ordered[i], pool, depths[i] = pool[:depth], pool[depth:], 0
	}

	for i, token := range t.tree {
		depth := token.next
		token.next = int32(i)
		ordered[depth][depths[depth]] = token
		depths[depth]++
	}
	t.ordered = ordered
	return ordered
}

type State32 struct {
	token32
	depths []int32
	leaf   bool
}

func (t *tokens32) PreOrder() (<-chan State32, [][]token32) {
	s, ordered := make(chan State32, 6), t.Order()
	go func() {
		var states [8]State32
		for i, _ := range states {
			states[i].depths = make([]int32, len(ordered))
		}
		depths, state, depth := make([]int32, len(ordered)), 0, 1
		write := func(t token32, leaf bool) {
			S := states[state]
			state, S.Rule, S.begin, S.end, S.next, S.leaf = (state+1)%8, t.Rule, t.begin, t.end, int32(depth), leaf
			copy(S.depths, depths)
			s <- S
		}

		states[state].token32 = ordered[0][0]
		depths[0]++
		state++
		a, b := ordered[depth-1][depths[depth-1]-1], ordered[depth][depths[depth]]
	depthFirstSearch:
		for {
			for {
				if i := depths[depth]; i > 0 {
					if c, j := ordered[depth][i-1], depths[depth-1]; a.isParentOf(c) &&
						(j < 2 || !ordered[depth-1][j-2].isParentOf(c)) {
						if c.end != b.begin {
							write(token32{Rule: Rule_In_, begin: c.end, end: b.begin}, true)
						}
						break
					}
				}

				if a.begin < b.begin {
					write(token32{Rule: RulePre_, begin: a.begin, end: b.begin}, true)
				}
				break
			}

			next := depth + 1
			if c := ordered[next][depths[next]]; c.Rule != RuleUnknown && b.isParentOf(c) {
				write(b, false)
				depths[depth]++
				depth, a, b = next, b, c
				continue
			}

			write(b, true)
			depths[depth]++
			c, parent := ordered[depth][depths[depth]], true
			for {
				if c.Rule != RuleUnknown && a.isParentOf(c) {
					b = c
					continue depthFirstSearch
				} else if parent && b.end != a.end {
					write(token32{Rule: Rule_Suf, begin: b.end, end: a.end}, true)
				}

				depth--
				if depth > 0 {
					a, b, c = ordered[depth-1][depths[depth-1]-1], a, ordered[depth][depths[depth]]
					parent = a.isParentOf(b)
					continue
				}

				break depthFirstSearch
			}
		}

		close(s)
	}()
	return s, ordered
}

func (t *tokens32) PrintSyntax() {
	tokens, ordered := t.PreOrder()
	max := -1
	for token := range tokens {
		if !token.leaf {
			fmt.Printf("%v", token.begin)
			for i, leaf, depths := 0, int(token.next), token.depths; i < leaf; i++ {
				fmt.Printf(" \x1B[36m%v\x1B[m", Rul3s[ordered[i][depths[i]-1].Rule])
			}
			fmt.Printf(" \x1B[36m%v\x1B[m\n", Rul3s[token.Rule])
		} else if token.begin == token.end {
			fmt.Printf("%v", token.begin)
			for i, leaf, depths := 0, int(token.next), token.depths; i < leaf; i++ {
				fmt.Printf(" \x1B[31m%v\x1B[m", Rul3s[ordered[i][depths[i]-1].Rule])
			}
			fmt.Printf(" \x1B[31m%v\x1B[m\n", Rul3s[token.Rule])
		} else {
			for c, end := token.begin, token.end; c < end; c++ {
				if i := int(c); max+1 < i {
					for j := max; j < i; j++ {
						fmt.Printf("skip %v %v\n", j, token.String())
					}
					max = i
				} else if i := int(c); i <= max {
					for j := i; j <= max; j++ {
						fmt.Printf("dupe %v %v\n", j, token.String())
					}
				} else {
					max = int(c)
				}
				fmt.Printf("%v", c)
				for i, leaf, depths := 0, int(token.next), token.depths; i < leaf; i++ {
					fmt.Printf(" \x1B[34m%v\x1B[m", Rul3s[ordered[i][depths[i]-1].Rule])
				}
				fmt.Printf(" \x1B[34m%v\x1B[m\n", Rul3s[token.Rule])
			}
			fmt.Printf("\n")
		}
	}
}

func (t *tokens32) PrintSyntaxTree(buffer string) {
	tokens, _ := t.PreOrder()
	for token := range tokens {
		for c := 0; c < int(token.next); c++ {
			fmt.Printf(" ")
		}
		fmt.Printf("\x1B[34m%v\x1B[m %v\n", Rul3s[token.Rule], strconv.Quote(buffer[token.begin:token.end]))
	}
}

func (t *tokens32) Add(rule Rule, begin, end, depth, index int) {
	t.tree[index] = token32{Rule: rule, begin: int32(begin), end: int32(end), next: int32(depth)}
}

func (t *tokens32) Tokens() <-chan token32 {
	s := make(chan token32, 16)
	go func() {
		for _, v := range t.tree {
			s <- v.GetToken32()
		}
		close(s)
	}()
	return s
}

func (t *tokens32) Error() []token32 {
	ordered := t.Order()
	length := len(ordered)
	tokens, length := make([]token32, length), length-1
	for i, _ := range tokens {
		o := ordered[length-i]
		if len(o) > 1 {
			tokens[i] = o[len(o)-2].GetToken32()
		}
	}
	return tokens
}

func (t *tokens16) Expand(index int) TokenTree {
	tree := t.tree
	if index >= len(tree) {
		expanded := make([]token32, 2*len(tree))
		for i, v := range tree {
			expanded[i] = v.GetToken32()
		}
		return &tokens32{tree: expanded}
	}
	return nil
}

func (t *tokens32) Expand(index int) TokenTree {
	tree := t.tree
	if index >= len(tree) {
		expanded := make([]token32, 2*len(tree))
		copy(expanded, tree)
		t.tree = expanded
	}
	return nil
}

type OrgMode struct {
	Buffer string
	buffer []rune
	rules  [23]func() bool
	Parse  func(rule ...int) error
	Reset  func()
	TokenTree
}

type textPosition struct {
	line, symbol int
}

type textPositionMap map[int]textPosition

func translatePositions(buffer string, positions []int) textPositionMap {
	length, translations, j, line, symbol := len(positions), make(textPositionMap, len(positions)), 0, 1, 0
	sort.Ints(positions)

search:
	for i, c := range buffer[0:] {
		if c == '\n' {
			line, symbol = line+1, 0
		} else {
			symbol++
		}
		if i == positions[j] {
			translations[positions[j]] = textPosition{line, symbol}
			for j++; j < length; j++ {
				if i != positions[j] {
					continue search
				}
			}
			break search
		}
	}

	return translations
}

type parseError struct {
	p *OrgMode
}

func (e *parseError) Error() string {
	tokens, error := e.p.TokenTree.Error(), "\n"
	positions, p := make([]int, 2*len(tokens)), 0
	for _, token := range tokens {
		positions[p], p = int(token.begin), p+1
		positions[p], p = int(token.end), p+1
	}
	translations := translatePositions(e.p.Buffer, positions)
	for _, token := range tokens {
		begin, end := int(token.begin), int(token.end)
		error += fmt.Sprintf("parse error near \x1B[34m%v\x1B[m (line %v symbol %v - line %v symbol %v):\n%v\n",
			Rul3s[token.Rule],
			translations[begin].line, translations[begin].symbol,
			translations[end].line, translations[end].symbol,
			/*strconv.Quote(*/ e.p.Buffer[begin:end] /*)*/)
	}

	return error
}

func (p *OrgMode) PrintSyntaxTree() {
	p.TokenTree.PrintSyntaxTree(p.Buffer)
}

func (p *OrgMode) Highlighter() {
	p.TokenTree.PrintSyntax()
}

func (p *OrgMode) Init() {
	p.buffer = []rune(p.Buffer)
	if len(p.buffer) == 0 || p.buffer[len(p.buffer)-1] != END_SYMBOL {
		p.buffer = append(p.buffer, END_SYMBOL)
	}

	var tree TokenTree = &tokens16{tree: make([]token16, math.MaxInt16)}
	position, depth, tokenIndex, buffer, rules := 0, 0, 0, p.buffer, p.rules

	p.Parse = func(rule ...int) error {
		r := 1
		if len(rule) > 0 {
			r = rule[0]
		}
		matches := p.rules[r]()
		p.TokenTree = tree
		if matches {
			p.TokenTree.trim(tokenIndex)
			return nil
		}
		return &parseError{p}
	}

	p.Reset = func() {
		position, tokenIndex, depth = 0, 0, 0
	}

	add := func(rule Rule, begin int) {
		if t := tree.Expand(tokenIndex); t != nil {
			tree = t
		}
		tree.Add(rule, begin, position, depth, tokenIndex)
		tokenIndex++
	}

	matchDot := func() bool {
		if buffer[position] != END_SYMBOL {
			position++
			return true
		}
		return false
	}

	/*matchChar := func(c byte) bool {
		if buffer[position] == c {
			position++
			return true
		}
		return false
	}*/

	/*matchRange := func(lower byte, upper byte) bool {
		if c := buffer[position]; c >= lower && c <= upper {
			position++
			return true
		}
		return false
	}*/

	rules = [...]func() bool{
		nil,
		/* 0 Start <- <((Markup / Content)* / EOF)> */
		func() bool {
			position0, tokenIndex0, depth0 := position, tokenIndex, depth
			{
				position1 := position
				depth++
				{
					position2, tokenIndex2, depth2 := position, tokenIndex, depth
				l4:
					{
						position5, tokenIndex5, depth5 := position, tokenIndex, depth
						{
							position6, tokenIndex6, depth6 := position, tokenIndex, depth
							if !rules[RuleMarkup]() {
								goto l7
							}
							goto l6
						l7:
							position, tokenIndex, depth = position6, tokenIndex6, depth6
							if !rules[RuleContent]() {
								goto l5
							}
						}
					l6:
						goto l4
					l5:
						position, tokenIndex, depth = position5, tokenIndex5, depth5
					}
					goto l2
					position, tokenIndex, depth = position2, tokenIndex2, depth2
					if !rules[RuleEOF]() {
						goto l0
					}
				}
			l2:
				depth--
				add(RuleStart, position1)
			}
			return true
		l0:
			position, tokenIndex, depth = position0, tokenIndex0, depth0
			return false
		},
		/* 1 Markup <- <(OrgNode / Properties)> */
		func() bool {
			position8, tokenIndex8, depth8 := position, tokenIndex, depth
			{
				position9 := position
				depth++
				{
					position10, tokenIndex10, depth10 := position, tokenIndex, depth
					if !rules[RuleOrgNode]() {
						goto l11
					}
					goto l10
				l11:
					position, tokenIndex, depth = position10, tokenIndex10, depth10
					if !rules[RuleProperties]() {
						goto l8
					}
				}
			l10:
				depth--
				add(RuleMarkup, position9)
			}
			return true
		l8:
			position, tokenIndex, depth = position8, tokenIndex8, depth8
			return false
		},
		/* 2 Headline <- <(Stars _ HeadlineText)> */
		func() bool {
			position12, tokenIndex12, depth12 := position, tokenIndex, depth
			{
				position13 := position
				depth++
				if !rules[RuleStars]() {
					goto l12
				}
				if !rules[Rule_]() {
					goto l12
				}
				if !rules[RuleHeadlineText]() {
					goto l12
				}
				depth--
				add(RuleHeadline, position13)
			}
			return true
		l12:
			position, tokenIndex, depth = position12, tokenIndex12, depth12
			return false
		},
		/* 3 OrgNode <- <(Headline LineEnd)> */
		func() bool {
			position14, tokenIndex14, depth14 := position, tokenIndex, depth
			{
				position15 := position
				depth++
				if !rules[RuleHeadline]() {
					goto l14
				}
				if !rules[RuleLineEnd]() {
					goto l14
				}
				depth--
				add(RuleOrgNode, position15)
			}
			return true
		l14:
			position, tokenIndex, depth = position14, tokenIndex14, depth14
			return false
		},
		/* 4 ContentLine <- <(!Markup <(!LineEnd .)+> LineEnd?)> */
		func() bool {
			position16, tokenIndex16, depth16 := position, tokenIndex, depth
			{
				position17 := position
				depth++
				{
					position18, tokenIndex18, depth18 := position, tokenIndex, depth
					if !rules[RuleMarkup]() {
						goto l18
					}
					goto l16
				l18:
					position, tokenIndex, depth = position18, tokenIndex18, depth18
				}
				{
					position19 := position
					depth++
					{
						position22, tokenIndex22, depth22 := position, tokenIndex, depth
						if !rules[RuleLineEnd]() {
							goto l22
						}
						goto l16
					l22:
						position, tokenIndex, depth = position22, tokenIndex22, depth22
					}
					if !matchDot() {
						goto l16
					}
				l20:
					{
						position21, tokenIndex21, depth21 := position, tokenIndex, depth
						{
							position23, tokenIndex23, depth23 := position, tokenIndex, depth
							if !rules[RuleLineEnd]() {
								goto l23
							}
							goto l21
						l23:
							position, tokenIndex, depth = position23, tokenIndex23, depth23
						}
						if !matchDot() {
							goto l21
						}
						goto l20
					l21:
						position, tokenIndex, depth = position21, tokenIndex21, depth21
					}
					depth--
					add(RulePegText, position19)
				}
				{
					position24, tokenIndex24, depth24 := position, tokenIndex, depth
					if !rules[RuleLineEnd]() {
						goto l24
					}
					goto l25
				l24:
					position, tokenIndex, depth = position24, tokenIndex24, depth24
				}
			l25:
				depth--
				add(RuleContentLine, position17)
			}
			return true
		l16:
			position, tokenIndex, depth = position16, tokenIndex16, depth16
			return false
		},
		/* 5 Content <- <(ContentLine / LineEnd)+> */
		func() bool {
			position26, tokenIndex26, depth26 := position, tokenIndex, depth
			{
				position27 := position
				depth++
				{
					position30, tokenIndex30, depth30 := position, tokenIndex, depth
					if !rules[RuleContentLine]() {
						goto l31
					}
					goto l30
				l31:
					position, tokenIndex, depth = position30, tokenIndex30, depth30
					if !rules[RuleLineEnd]() {
						goto l26
					}
				}
			l30:
			l28:
				{
					position29, tokenIndex29, depth29 := position, tokenIndex, depth
					{
						position32, tokenIndex32, depth32 := position, tokenIndex, depth
						if !rules[RuleContentLine]() {
							goto l33
						}
						goto l32
					l33:
						position, tokenIndex, depth = position32, tokenIndex32, depth32
						if !rules[RuleLineEnd]() {
							goto l29
						}
					}
				l32:
					goto l28
				l29:
					position, tokenIndex, depth = position29, tokenIndex29, depth29
				}
				depth--
				add(RuleContent, position27)
			}
			return true
		l26:
			position, tokenIndex, depth = position26, tokenIndex26, depth26
			return false
		},
		/* 6 HeadlineText <- <<(!LineEnd .)+>> */
		func() bool {
			position34, tokenIndex34, depth34 := position, tokenIndex, depth
			{
				position35 := position
				depth++
				{
					position36 := position
					depth++
					{
						position39, tokenIndex39, depth39 := position, tokenIndex, depth
						if !rules[RuleLineEnd]() {
							goto l39
						}
						goto l34
					l39:
						position, tokenIndex, depth = position39, tokenIndex39, depth39
					}
					if !matchDot() {
						goto l34
					}
				l37:
					{
						position38, tokenIndex38, depth38 := position, tokenIndex, depth
						{
							position40, tokenIndex40, depth40 := position, tokenIndex, depth
							if !rules[RuleLineEnd]() {
								goto l40
							}
							goto l38
						l40:
							position, tokenIndex, depth = position40, tokenIndex40, depth40
						}
						if !matchDot() {
							goto l38
						}
						goto l37
					l38:
						position, tokenIndex, depth = position38, tokenIndex38, depth38
					}
					depth--
					add(RulePegText, position36)
				}
				depth--
				add(RuleHeadlineText, position35)
			}
			return true
		l34:
			position, tokenIndex, depth = position34, tokenIndex34, depth34
			return false
		},
		/* 7 Stars <- <(('*' '*' '*') / ('*' '*') / '*')> */
		func() bool {
			position41, tokenIndex41, depth41 := position, tokenIndex, depth
			{
				position42 := position
				depth++
				{
					position43, tokenIndex43, depth43 := position, tokenIndex, depth
					if buffer[position] != rune('*') {
						goto l44
					}
					position++
					if buffer[position] != rune('*') {
						goto l44
					}
					position++
					if buffer[position] != rune('*') {
						goto l44
					}
					position++
					goto l43
				l44:
					position, tokenIndex, depth = position43, tokenIndex43, depth43
					if buffer[position] != rune('*') {
						goto l45
					}
					position++
					if buffer[position] != rune('*') {
						goto l45
					}
					position++
					goto l43
				l45:
					position, tokenIndex, depth = position43, tokenIndex43, depth43
					if buffer[position] != rune('*') {
						goto l41
					}
					position++
				}
			l43:
				depth--
				add(RuleStars, position42)
			}
			return true
		l41:
			position, tokenIndex, depth = position41, tokenIndex41, depth41
			return false
		},
		/* 8 PropertiesBegin <- <(_ (':' 'P' 'R' 'O' 'P' 'E' 'R' 'T' 'I' 'E' 'S' ':') _ LineEnd)> */
		func() bool {
			position46, tokenIndex46, depth46 := position, tokenIndex, depth
			{
				position47 := position
				depth++
				if !rules[Rule_]() {
					goto l46
				}
				if buffer[position] != rune(':') {
					goto l46
				}
				position++
				if buffer[position] != rune('P') {
					goto l46
				}
				position++
				if buffer[position] != rune('R') {
					goto l46
				}
				position++
				if buffer[position] != rune('O') {
					goto l46
				}
				position++
				if buffer[position] != rune('P') {
					goto l46
				}
				position++
				if buffer[position] != rune('E') {
					goto l46
				}
				position++
				if buffer[position] != rune('R') {
					goto l46
				}
				position++
				if buffer[position] != rune('T') {
					goto l46
				}
				position++
				if buffer[position] != rune('I') {
					goto l46
				}
				position++
				if buffer[position] != rune('E') {
					goto l46
				}
				position++
				if buffer[position] != rune('S') {
					goto l46
				}
				position++
				if buffer[position] != rune(':') {
					goto l46
				}
				position++
				if !rules[Rule_]() {
					goto l46
				}
				if !rules[RuleLineEnd]() {
					goto l46
				}
				depth--
				add(RulePropertiesBegin, position47)
			}
			return true
		l46:
			position, tokenIndex, depth = position46, tokenIndex46, depth46
			return false
		},
		/* 9 PropertiesEnd <- <(_ (':' 'E' 'N' 'D' ':') _ LineEnd?)> */
		func() bool {
			position48, tokenIndex48, depth48 := position, tokenIndex, depth
			{
				position49 := position
				depth++
				if !rules[Rule_]() {
					goto l48
				}
				if buffer[position] != rune(':') {
					goto l48
				}
				position++
				if buffer[position] != rune('E') {
					goto l48
				}
				position++
				if buffer[position] != rune('N') {
					goto l48
				}
				position++
				if buffer[position] != rune('D') {
					goto l48
				}
				position++
				if buffer[position] != rune(':') {
					goto l48
				}
				position++
				if !rules[Rule_]() {
					goto l48
				}
				{
					position50, tokenIndex50, depth50 := position, tokenIndex, depth
					if !rules[RuleLineEnd]() {
						goto l50
					}
					goto l51
				l50:
					position, tokenIndex, depth = position50, tokenIndex50, depth50
				}
			l51:
				depth--
				add(RulePropertiesEnd, position49)
			}
			return true
		l48:
			position, tokenIndex, depth = position48, tokenIndex48, depth48
			return false
		},
		/* 10 Properties <- <(PropertiesBegin PropertyPair* PropertiesEnd)> */
		func() bool {
			position52, tokenIndex52, depth52 := position, tokenIndex, depth
			{
				position53 := position
				depth++
				if !rules[RulePropertiesBegin]() {
					goto l52
				}
			l54:
				{
					position55, tokenIndex55, depth55 := position, tokenIndex, depth
					if !rules[RulePropertyPair]() {
						goto l55
					}
					goto l54
				l55:
					position, tokenIndex, depth = position55, tokenIndex55, depth55
				}
				if !rules[RulePropertiesEnd]() {
					goto l52
				}
				depth--
				add(RuleProperties, position53)
			}
			return true
		l52:
			position, tokenIndex, depth = position52, tokenIndex52, depth52
			return false
		},
		/* 11 PropertyPair <- <(_ PropertyKey _ PropertyValue _)> */
		func() bool {
			position56, tokenIndex56, depth56 := position, tokenIndex, depth
			{
				position57 := position
				depth++
				if !rules[Rule_]() {
					goto l56
				}
				if !rules[RulePropertyKey]() {
					goto l56
				}
				if !rules[Rule_]() {
					goto l56
				}
				if !rules[RulePropertyValue]() {
					goto l56
				}
				if !rules[Rule_]() {
					goto l56
				}
				depth--
				add(RulePropertyPair, position57)
			}
			return true
		l56:
			position, tokenIndex, depth = position56, tokenIndex56, depth56
			return false
		},
		/* 12 PropertyKeyChar <- <(IdentifierChar / '-')> */
		func() bool {
			position58, tokenIndex58, depth58 := position, tokenIndex, depth
			{
				position59 := position
				depth++
				{
					position60, tokenIndex60, depth60 := position, tokenIndex, depth
					if !rules[RuleIdentifierChar]() {
						goto l61
					}
					goto l60
				l61:
					position, tokenIndex, depth = position60, tokenIndex60, depth60
					if buffer[position] != rune('-') {
						goto l58
					}
					position++
				}
			l60:
				depth--
				add(RulePropertyKeyChar, position59)
			}
			return true
		l58:
			position, tokenIndex, depth = position58, tokenIndex58, depth58
			return false
		},
		/* 13 PropertyKey <- <(!PropertiesEnd ':' <PropertyKeyChar+> ':')> */
		func() bool {
			position62, tokenIndex62, depth62 := position, tokenIndex, depth
			{
				position63 := position
				depth++
				{
					position64, tokenIndex64, depth64 := position, tokenIndex, depth
					if !rules[RulePropertiesEnd]() {
						goto l64
					}
					goto l62
				l64:
					position, tokenIndex, depth = position64, tokenIndex64, depth64
				}
				if buffer[position] != rune(':') {
					goto l62
				}
				position++
				{
					position65 := position
					depth++
					if !rules[RulePropertyKeyChar]() {
						goto l62
					}
				l66:
					{
						position67, tokenIndex67, depth67 := position, tokenIndex, depth
						if !rules[RulePropertyKeyChar]() {
							goto l67
						}
						goto l66
					l67:
						position, tokenIndex, depth = position67, tokenIndex67, depth67
					}
					depth--
					add(RulePegText, position65)
				}
				if buffer[position] != rune(':') {
					goto l62
				}
				position++
				depth--
				add(RulePropertyKey, position63)
			}
			return true
		l62:
			position, tokenIndex, depth = position62, tokenIndex62, depth62
			return false
		},
		/* 14 PropertyValue <- <((!LineEnd .)* LineEnd)> */
		func() bool {
			position68, tokenIndex68, depth68 := position, tokenIndex, depth
			{
				position69 := position
				depth++
			l70:
				{
					position71, tokenIndex71, depth71 := position, tokenIndex, depth
					{
						position72, tokenIndex72, depth72 := position, tokenIndex, depth
						if !rules[RuleLineEnd]() {
							goto l72
						}
						goto l71
					l72:
						position, tokenIndex, depth = position72, tokenIndex72, depth72
					}
					if !matchDot() {
						goto l71
					}
					goto l70
				l71:
					position, tokenIndex, depth = position71, tokenIndex71, depth71
				}
				if !rules[RuleLineEnd]() {
					goto l68
				}
				depth--
				add(RulePropertyValue, position69)
			}
			return true
		l68:
			position, tokenIndex, depth = position68, tokenIndex68, depth68
			return false
		},
		/* 15 IdentifierChar <- <([a-z] / [A-Z] / '_')> */
		func() bool {
			position73, tokenIndex73, depth73 := position, tokenIndex, depth
			{
				position74 := position
				depth++
				{
					position75, tokenIndex75, depth75 := position, tokenIndex, depth
					if c := buffer[position]; c < rune('a') || c > rune('z') {
						goto l76
					}
					position++
					goto l75
				l76:
					position, tokenIndex, depth = position75, tokenIndex75, depth75
					if c := buffer[position]; c < rune('A') || c > rune('Z') {
						goto l77
					}
					position++
					goto l75
				l77:
					position, tokenIndex, depth = position75, tokenIndex75, depth75
					if buffer[position] != rune('_') {
						goto l73
					}
					position++
				}
			l75:
				depth--
				add(RuleIdentifierChar, position74)
			}
			return true
		l73:
			position, tokenIndex, depth = position73, tokenIndex73, depth73
			return false
		},
		/* 16 _ <- <WhiteSpace*> */
		func() bool {
			{
				position79 := position
				depth++
			l80:
				{
					position81, tokenIndex81, depth81 := position, tokenIndex, depth
					if !rules[RuleWhiteSpace]() {
						goto l81
					}
					goto l80
				l81:
					position, tokenIndex, depth = position81, tokenIndex81, depth81
				}
				depth--
				add(Rule_, position79)
			}
			return true
		},
		/* 17 __ <- <(WhiteSpace / LineEnd)*> */
		nil,
		/* 18 LineEnd <- <('\r' / '\n')> */
		func() bool {
			position83, tokenIndex83, depth83 := position, tokenIndex, depth
			{
				position84 := position
				depth++
				{
					position85, tokenIndex85, depth85 := position, tokenIndex, depth
					if buffer[position] != rune('\r') {
						goto l86
					}
					position++
					goto l85
				l86:
					position, tokenIndex, depth = position85, tokenIndex85, depth85
					if buffer[position] != rune('\n') {
						goto l83
					}
					position++
				}
			l85:
				depth--
				add(RuleLineEnd, position84)
			}
			return true
		l83:
			position, tokenIndex, depth = position83, tokenIndex83, depth83
			return false
		},
		/* 19 WhiteSpace <- <('\t' / ' ')> */
		func() bool {
			position87, tokenIndex87, depth87 := position, tokenIndex, depth
			{
				position88 := position
				depth++
				{
					position89, tokenIndex89, depth89 := position, tokenIndex, depth
					if buffer[position] != rune('\t') {
						goto l90
					}
					position++
					goto l89
				l90:
					position, tokenIndex, depth = position89, tokenIndex89, depth89
					if buffer[position] != rune(' ') {
						goto l87
					}
					position++
				}
			l89:
				depth--
				add(RuleWhiteSpace, position88)
			}
			return true
		l87:
			position, tokenIndex, depth = position87, tokenIndex87, depth87
			return false
		},
		/* 20 EOF <- <!.> */
		func() bool {
			position91, tokenIndex91, depth91 := position, tokenIndex, depth
			{
				position92 := position
				depth++
				{
					position93, tokenIndex93, depth93 := position, tokenIndex, depth
					if !matchDot() {
						goto l93
					}
					goto l91
				l93:
					position, tokenIndex, depth = position93, tokenIndex93, depth93
				}
				depth--
				add(RuleEOF, position92)
			}
			return true
		l91:
			position, tokenIndex, depth = position91, tokenIndex91, depth91
			return false
		},
		nil,
	}
	p.rules = rules
}
