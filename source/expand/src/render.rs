//! Token-stream pretty-printing for human consumption.
//!
//! Renders a `TokenStream` as indented text. Feeds the expansion snapshot tests and the
//! `VERUS_SPEC_CHECK_PRINT_EXPANSION` hook in [`crate::expand`].

use proc_macro2::{Delimiter, Group, Spacing, TokenStream, TokenTree};

#[derive(Clone, Copy, PartialEq)]
enum P {
    /// Glued to what follows: `::`, `.`, `#`
    Tight(char),
    /// Ident, literal, or closing delimiter
    Word,
    /// Capitalized ident: a following `<` opens generics
    Type,
    /// A spaced operator, including `,` and `;`
    Op,
}

struct R {
    out: String,
    prev: P,
    angle: u32,
}

pub fn pretty_tokens(ts: &TokenStream) -> String {
    let mut r = R {
        out: String::new(),
        prev: P::Tight('\0'),
        angle: 0,
    };
    r.go(ts.clone(), 0, true);
    if !r.out.ends_with('\n') {
        r.out.push('\n');
    }
    r.out
}

impl R {
    fn fresh(&self) -> bool {
        self.out.is_empty() || self.out.ends_with('\n')
    }

    /// True when the previous token glues to whatever comes next.
    fn tight(&self) -> bool {
        matches!(self.prev, P::Tight(_))
    }

    fn operand(&self) -> bool {
        matches!(self.prev, P::Word | P::Type)
    }

    fn put(&mut self, s: &str, ind: usize, space: bool, prev: P) {
        if self.fresh() {
            for _ in 0..ind {
                self.out.push_str("    ");
            }
        } else if space {
            self.out.push(' ');
        }
        self.out.push_str(s);
        self.prev = prev;
    }

    fn nl(&mut self) {
        if !self.fresh() {
            self.out.push('\n');
        }
        self.prev = P::Tight('\0');
    }

    fn go(&mut self, ts: TokenStream, ind: usize, stmt: bool) {
        let mut it = ts.into_iter().peekable();
        while let Some(tt) = it.next() {
            match tt {
                TokenTree::Group(g) => {
                    // May a closing `}` keep its line?
                    let join = match it.peek() {
                        Some(TokenTree::Ident(i)) => i == "else",
                        Some(TokenTree::Punct(p)) => matches!(p.as_char(), ',' | ';' | '.'),
                        _ => false,
                    };
                    self.group(&g, ind, stmt, join);
                }
                TokenTree::Ident(id) => {
                    let s = id.to_string();
                    let k = if s.starts_with(char::is_uppercase) {
                        P::Type
                    } else {
                        P::Word
                    };
                    let sp = !self.tight();
                    self.put(&s, ind, sp, k);
                }
                TokenTree::Literal(l) => {
                    let sp = !self.tight();
                    self.put(&l.to_string(), ind, sp, P::Word);
                }
                TokenTree::Punct(p) => {
                    let (c, joint) = (p.as_char(), p.spacing() == Spacing::Joint);

                    // Fold `::`, so a lone `:` (`num: u32`) stays spaced.
                    if c == ':'
                        && joint
                        && matches!(it.peek(), Some(TokenTree::Punct(n)) if n.as_char() == ':')
                    {
                        it.next();
                        self.put("::", ind, false, P::Tight(':'));
                        continue;
                    }
                    // Generic close, guarded against the `>` of `->` / `=>`.
                    if c == '>' && self.angle > 0 && !matches!(self.prev, P::Tight(x) if x != '>') {
                        self.angle -= 1;
                        let k = if joint { P::Tight('>') } else { P::Word };
                        self.put(">", ind, false, k);
                        continue;
                    }
                    // Generic open: turbofish or capitalized type name.
                    if c == '<' && matches!(self.prev, P::Type | P::Tight(':')) {
                        self.angle += 1;
                        self.put("<", ind, false, P::Tight('<'));
                        continue;
                    }

                    let bang = c == '!'
                        && self.operand()
                        && matches!(it.peek(), Some(TokenTree::Group(_)));
                    // Prefix vs binary, by whether an operand just ended.
                    let prefix = matches!(c, '&' | '*' | '-' | '+' | '!') && !self.operand();
                    let sp = !self.tight();
                    let (sp, k) = match c {
                        _ if bang => (false, P::Tight('!')),
                        '.' => (false, P::Tight('.')),
                        ',' | ';' => (false, P::Op),
                        '#' => (sp, P::Tight('#')),
                        _ if joint || prefix => (sp, P::Tight(c)),
                        _ => (sp, P::Op),
                    };
                    self.put(&c.to_string(), ind, sp, k);

                    // Break statements and struct/match fields — but not
                    // inside parens, so `[AtomicBool; N]` stays inline.
                    if stmt && !joint && (c == ';' || c == ',') {
                        self.nl();
                    }
                }
            }
        }
    }

    fn group(&mut self, g: &Group, ind: usize, stmt: bool, join: bool) {
        let d = g.delimiter();
        // Invisible `quote!` interpolation groups contribute no spacing.
        if d == Delimiter::None {
            return self.go(g.stream(), ind, stmt);
        }
        let attr = d == Delimiter::Bracket && self.prev == P::Tight('#');
        let (o, c) = match d {
            Delimiter::Brace => ("{", "}"),
            Delimiter::Bracket => ("[", "]"),
            _ => ("(", ")"),
        };
        // `f(x)` and `a[i]` hug; `-> T {` does not.
        let sp = !self.tight() && (d == Delimiter::Brace || !self.operand());

        if d == Delimiter::Brace {
            if g.stream().is_empty() {
                self.put("{}", ind, sp, P::Word);
            } else {
                self.put(o, ind, sp, P::Tight('{'));
                self.nl();
                self.go(g.stream(), ind + 1, true);
                self.nl();
                self.put(c, ind, false, P::Word);
            }
            if stmt && !join {
                self.nl();
            }
        } else {
            // Same indent: a paren group continues the current line. A brace
            // group inside it still breaks, which is what closures want.
            self.put(o, ind, sp, P::Tight('('));
            self.go(g.stream(), ind, false);
            self.put(c, ind, false, P::Word);
            if attr && stmt {
                self.nl();
            }
        }
    }
}
