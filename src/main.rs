#![allow(dead_code)]

use itertools::Itertools;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Term{
    Lambda(Box<Term>),
    App(Box<Term>, Box<Term>),
    Index(u8)
}

use Term::*;

fn term_size(term: &Term) -> u32 {
    match term {
        Term::Lambda(x) => 2 + term_size(x),
        Term::App(x, y) => 2 + term_size(x) + term_size(y),
        Term::Index(n) => (n + 1).into(),
    }
}

fn term_openness(term: &Term) -> u8 {
    match term {
        Term::Lambda(x) => {
            let x_openness = term_openness(x);
            if x_openness == 0 {
                0
            } else {
                x_openness - 1
            }
        }
        Term::App(x, y) => term_openness(x).max(term_openness(y)),
        /*  */Term::Index(n) => *n,
    }
}

fn is_closed(term: &Term) -> bool {
    term_openness(term) == 0
}

fn re_de_bruijn_substituent_recur(body_level: u8, substituent: &Term, substituent_level: u8) -> Term {
    assert!(body_level > 0);
    if body_level == 1 { 
        return substituent.clone() 
    };
    match substituent {
        Index(n) => 
            if *n > substituent_level {Index(n + body_level - 1)} else {Index(*n)},
        Lambda(x) => 
            Lambda(Box::new(
                re_de_bruijn_substituent_recur(body_level, x, substituent_level+1)
            )),
        App(x, y) => 
            App(Box::new(re_de_bruijn_substituent_recur(body_level, x, substituent_level)),
                Box::new(re_de_bruijn_substituent_recur(body_level, y, substituent_level))
            ),
    }
}

fn re_de_bruijn_substituent(level: u8, substituent: &Term) -> Term {
    re_de_bruijn_substituent_recur(level, substituent, 0)
}

fn substitute_level(body: Term, substituent: &Term, level: u8) -> Term {
    match body {
        Index(n) => {
            if n == level {
                re_de_bruijn_substituent(level, substituent)
            } else if n > level {
                // in something like λ6, we need to take into account that there is 
                // one fewer lambda between the variable and its target now
                assert!(n != 1, "body {} substi {} level {}", print_term(&body), print_term(&substituent), level);
                Index(n-1)
            } else {
                // whereas in something like λλλ1, we don't need to change the 1
                Index(n) 
            }
        },
        Lambda(x) => Lambda(Box::new(substitute_level(*x, substituent, level+1))),
        App(x, y) => 
            App(Box::new(substitute_level(*x, substituent, level)), 
                Box::new(substitute_level(*y, substituent, level)))
    }
}


// if you have a term like (λT) S then body is T and substituent is S 
fn substitute(body: Term, substituent: &Term) -> Term {
    // dbg!(format!("substituting {} into {}", print_term(substituent), print_term(&body)));
    let ans = substitute_level(body, &substituent, 1);
    // dbg!(format!("ans: {}", print_term(&ans)));
    ans
}

// weak head normal form, E := (\x -> term) or (x term_1 . . . term_n)
// returns none if there is no reduction
fn whnf_reduce_step(term: Term) -> Option<Term> {
    match term {
        Lambda(_) => None,
        Index(_) => None,
        App(x, y) => {
            // we might need to reduce two things. first, reduce x to whnf. second, 
            // if that x is a lambda, then we need to substitute. 
            if let Some(x_reduced) = whnf_reduce_step(*x.clone()) {
                Some(App(Box::new(x_reduced), y))
            } else {
                match *x {
                    App(_, _) => None,
                    Index(_) => None,
                    Lambda(z) => Some(substitute(*z, &y)),
                }
            }
        },
    }
}

fn whnf_reduce(mut term: Term, reduce_limit: u32) -> (Term, u32) {
    let mut counter = 0; 
    while let Some(reduced_term) = whnf_reduce_step(term.clone()) {
        term = reduced_term;
        counter += 1;
        if counter == reduce_limit {
            break
        }
    }
    (term, counter)
}

// normal form, ie E = (\x. E) or x E_1 . . . E_n
// returns None if there is no reduction
fn nf_reduce_step(term: Term) -> Option<Term> {
    match term {
        Index(_) => None,
        Lambda(x) => if let Some(new_term) = nf_reduce_step(*x) {
            Some(Lambda(Box::new(new_term)))
        } else {
            None
        },
        App(x, y) => {
            // first reduce x to whnf, if it becomes a lambda, then substitute. 
            // otherwise, reduce first x, then y to nf. 
            if let Some(x_reduced) = whnf_reduce_step(*x.clone()) {
                Some(App(Box::new(x_reduced), y))
            } else if let Lambda(z) = *x.clone() {
                Some(substitute(*z, &y))
            } else if let Some(x_reduced) = nf_reduce_step(*x.clone()) {
                Some(App(Box::new(x_reduced), y))
            } else if let Some(y_reduced) = nf_reduce_step(*y.clone()) {
                Some(App(x, Box::new(y_reduced)))
            } else {
                None
            }
        },
    }
}

fn nf_reduce(term: &Term, reduce_limit: u32) -> (Term, u32) {
    let mut counter = 0;
    let mut cur_term = term.clone();
    while let Some(reduced_term) = nf_reduce_step(cur_term.clone()) {
        cur_term = reduced_term;
        counter += 1;
        if counter == reduce_limit {
            break
        }
    }
    (cur_term, counter)
}


/* 
    dp relation: count(0, *) = 0, count (1, *) = 0
    count(s, o) = 
          1 if s == o+1 else 0 
        + count(x-2, y+1) if o > 0 else (count(s-2, 0) + count(s-2, 1))
        + sum (z from 0 to x-2) {
            let left  = sum (p from 0 to o-1) count(z, p)
            let right = sum (p from 0 to o-1) count(x-2-z, p)
            count(z, o) * right + left * count(x-2-z, o) + count(z, o) * count(x-2-z, 0)
          }
*/
fn dp_counting_terms_of_size_open(target_size: usize, target_openness: usize) -> u64 {
    //size is the first index, openness is the second
    let mut table = vec![];
    for size in 0..=target_size {
        table.push(vec![]);
        let max_openness = target_openness + (target_size - size) / 2;
        for _ in 0..=max_openness {
            table[size].push(u64::MAX);
        }
    }
    for size in 0..=1.min(target_size) {
        let max_openness = target_openness + (target_size - size) / 2;
        for openness in 0..=max_openness {
            table[size][openness] = 0;
        }
    }
    for size in 2..=target_size {
        let max_openness = target_openness + (target_size - size) / 2;
        for openness in 0..=max_openness {
            let index_term_count = if size == openness + 1 {1} else {0};
            let lambda_term_count = if openness == 0 {
                table[size-2][0] + table[size-2][1]
            } else {
                table[size-2][openness+1]
            };
            let mut app_term_count = 0;
            for z in 0..=(size-2) {
                let mut left = 0;
                let mut right = 0;
                for sub_openness in 0..openness {
                    left += table[z][sub_openness];
                    right += table[size-2-z][sub_openness];
                }
                app_term_count += left * table[size-2-z][openness];
                app_term_count += table[z][openness] * right;
                app_term_count += table[z][openness] * table[size-2-z][openness];
            }
            // dbg!(size, openness, index_term_count, lambda_term_count, app_term_count);
            table[size][openness] = index_term_count + lambda_term_count + app_term_count;
        }
    }
    // dbg!(&table);
    table[target_size][target_openness]
}

/* 
    dp relation: count(0, *) = 0, count (1, *) = 0
    count(s, o) = 
          1 if s == o+1 else 0 
        + count(x-2, y+1) if o > 0 else (count(s-2, 0) + count(s-2, 1))
        + sum (z from 0 to x-2) {
            let left  = sum (p from 0 to o-1) count(z, p)
            let right = sum (p from 0 to o-1) count(x-2-z, p)
            count(z, o) * right + left * count(x-2-z, o) + count(z, o) * count(x-2-z, 0)
          }

The DP relation from the previous function applies almost verbatim here. Just, 
instead of adding to the count, we add terms to the vec. Then we return the table 
directly. 

Return type: Vec<Vec<Vec<Term>>>
The three indices are size, openness, and then a Vec<Term> listing all terms of that (s, o) pair. 
*/
fn dp_list_terms_of_size_open(target_size: usize, target_openness: usize) -> Vec<Vec<Vec<Term>>> {
    let mut table: Vec<Vec<Vec<Term>>> = vec![];
    for size in 0..=target_size {
        table.push(vec![]);
        let max_openness = target_openness + (target_size - size) / 2;
        for _ in 0..=max_openness {
            table[size].push(vec![]);
        }
    }
    // we don't need the size 0, 1 basecase, because the vectors start empty,
    // which is the basecase in question

    for size in 2..=target_size {
        let max_openness = target_openness + (target_size - size) / 2;
        for openness in 0..=max_openness {
            let mut new_term_list = vec![];
            // index term case
            if size == openness + 1 
                {new_term_list.push(Index(openness.try_into().unwrap()))}
            
            // lambda term case
            if openness == 0 {
                for smaller_term in &table[size-2][0] {
                    new_term_list.push(Lambda(Box::new(smaller_term.clone())))
                }
                for smaller_term in &table[size-2][1] {
                    new_term_list.push(Lambda(Box::new(smaller_term.clone())))
                }
            } else {
                for smaller_term in &table[size-2][openness+1] {
                    new_term_list.push(Lambda(Box::new(smaller_term.clone())))
                }
            }

            // app term case
            for z in 0..=(size-2) {
                let mut left = vec![];
                let mut right = vec![];
                for sub_openness in 0..openness {
                    for left_term in &table[z][sub_openness] {
                        left.push(left_term)
                    }
                    for right_term in &table[size-2-z][sub_openness] {
                        right.push(right_term)
                    }
                }
                // left * table[size-2-z][openness];
                for (x, y) in left.into_iter().cartesian_product(&table[size-2-z][openness]) {
                    new_term_list.push(App(
                        Box::new(x.clone()), Box::new(y.clone())))
                }
                // table[z][openness] * right;
                for (x, y) in right.into_iter().cartesian_product(&table[z][openness]) {
                    new_term_list.push(App(
                        Box::new(x.clone()), Box::new(y.clone())))
                }
                // table[z][openness] * table[size-2-z][openness];
                for (x, y) in (&table[z][openness]).into_iter().cartesian_product(&table[size-2-z][openness]) {
                    new_term_list.push(App(
                        Box::new(x.clone()), Box::new(y.clone())))
                }
            }
         // dbg!(size, openness, index_term_count, lambda_term_count, app_term_count);
         table[size][openness] = new_term_list;
        }
    }
    // dbg!(&table);
    table
}


type Foo = (Term, Term);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct UnsolvedData {reduce_nf: Option<(Term, u32)>}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum TermRes {
    Unsolved(UnsolvedData),
    /*
    the normal form
    the number of steps to get there
    the size of the normal form
    */
    Reduced(Term, u32, u32),
    // the number of steps to nf-red the term for to see that it loops
    Looped(u32),
}
use TermRes::*;

/*
attempt to reduce all terms to normal form. 
return value: the original term, plus the output TermRes. 
the output is Unsolved if no normal form was found, and gives the term reduced for the max steps in the option
the output is Reduced if a normal form was found
*/
fn reduce_list_of_terms(terms: Vec<Term>, reduce_limit: u32) 
    -> Vec<(Term, TermRes)>
{
    let mut out = vec![];
    for term in terms {
        let (red_term, steps) = nf_reduce(&term, reduce_limit);
        if steps == reduce_limit {
            // we failed
            out.push((term, Unsolved(UnsolvedData { reduce_nf: Some((red_term, reduce_limit)) })));
        } else {
            // normal form found
            let term_size = term_size(&red_term);
            out.push((term, Reduced(red_term, steps, term_size)));
        }
    }
    out
}

fn check_loop(term: Term, ud: UnsolvedData, loop_limit: u32) -> (Term, TermRes) {
    let orig_term = term.clone();
    let mut red_term = match nf_reduce_step(term) {
        None => panic!("loop limit should be smaller than reduce limit"),
        Some(red_term) => red_term,
    };
    // step count is now 1 
    for step_count in 1..loop_limit {
        if red_term == orig_term {
            return (orig_term, Looped(step_count))
        } else {
            red_term = match nf_reduce_step(red_term) {
                None => panic!("loop limit should be smaller than reduce limit"),
                Some(red_term) => red_term,
            };
        }
    }
    (orig_term, Unsolved(ud))
}

fn check_loops(terms: Vec<(Term, TermRes)>, loop_limit: u32) -> Vec<(Term, TermRes)> {
    let mut out = vec![];
    for (term, prev_res) in terms {
        match prev_res {
            Reduced(_, _, _) => out.push((term, prev_res)),
            Unsolved(ud) => out.push(check_loop(term, ud, loop_limit)),
            Looped(_) => panic!("shouldn't loop yet lol")
        }
    }
    out
} 

fn print_term(term: &Term) -> String {
    match term {
        Index(n) => n.to_string(),
        Lambda(x) => "λ".to_owned() + &print_term(x),
        App(x, y) => format!("({}){}", print_term(x), print_term(y)),
    }
}

fn display_solved_term(t: &Term, r: &Term, steps: u32, size: u32) {
    println!("{} reduced to {} in {} steps (output size: {})", print_term(t), print_term(r), steps, size)
}

fn display_unsolved_term(t: &Term, r: &Term, step_limit: u32) {
    println!("{} reduced to {} (not in normal form) in {} steps", print_term(t), print_term(r), step_limit)
}
fn display_output(red_output: Vec<(Term, TermRes)> , step_limit: u32) {
    let total_len = red_output.len();
    
    // split into solved and holdouts 
    let mut nf_terms = vec![];
    let mut loop_terms = vec![];
    let mut unsolved = vec![];
    for output in red_output {
        match output {
            (t, Unsolved(UnsolvedData{reduce_nf: Some((r, _))})) => unsolved.push((t, r)),
            (t, Reduced(r, steps, size)) => nf_terms.push((t, r, steps, size)),
            (t, Looped(loop_len)) => loop_terms.push((t, loop_len)),
            _ => panic!("failed to match")
        }
    }

    let num_solved = nf_terms.len() + loop_terms.len();

    println!("There were {} terms, of which {} were solved and {} were unsolved", 
        total_len, num_solved, unsolved.len());
    if loop_terms.len() > 0 {
        println!("{} terms were solved by looping", loop_terms.len());
    }

    if nf_terms.len() > 0 {
    // show maximum reduction steps
    let mut sorted_by_steps = nf_terms.clone();
    sorted_by_steps.sort_by_key(|(_t, _r, steps, _size)|*steps);
    sorted_by_steps.reverse();
    println!("maximum reduction steps: {}", sorted_by_steps[0].2);
    // and three such longest terms
    for (t, r, steps, size) in &sorted_by_steps[0..3.min(sorted_by_steps.len())] {
        display_solved_term(t, r, *steps, *size)
    }

    // show maximum output size
    let mut sorted_by_size = nf_terms.clone();
    sorted_by_size.sort_by_key(|(_t, _r, _steps, size)|*size);
    sorted_by_size.reverse();
    println!("maximum output size: {}", sorted_by_size[0].3);
    // and three such largest terms 
    for (t, r, steps, size) in &sorted_by_size[0..3.min(sorted_by_size.len())] {
        display_solved_term(t, r, *steps, *size)
    }
    }

    // display number of holdouts
    println!("There were {} unsolved terms", unsolved.len());
    // display some holdouts
    for (t, r) in &unsolved[0..10.min(unsolved.len())] {
        display_unsolved_term(t, r, step_limit)
    }
}

enum Token {
    Lambda, 
    Open, 
    Close,
    Index(u8)
}

fn tokenize(term_string: String) -> Vec<Token> {
    let mut out = Vec::new();
    for s in term_string.chars() {
        match s {
            'λ' => out.push(Token::Lambda),
            '(' => out.push(Token::Open), 
            ')' => out.push(Token::Close),
            c => {
                if c.is_ascii_digit() && c != '0' {
                    out.push(Token::Index(c.to_digit(10).expect("we checked it is a digit") as u8))
                } else {
                    panic!("passed invalid charaacter {}", c)
                }
            }
        }
    }
    out
}

fn parse_tokens_recur(tokens: &[Token]) -> Option<(Term, &[Token])> {
    let first_token = tokens.first().expect("no parsing empty tokens");
    match first_token {
        Token::Lambda => {
            if tokens.len() == 1 {
                None
            } else {
                let (rest_term, rest_tokens) = parse_tokens_recur(&tokens[1..])?;
                Some((Lambda(Box::new(rest_term)), rest_tokens))
            }
        },
        Token::Index(n) => {
            Some((Index(*n), &tokens[1..]))
        },
        Token::Open => {
            let (term_a, rest_tokens) = parse_tokens_recur(&tokens[1..])?;
            if let Some(Token::Close) = rest_tokens.first() {
                let (term_b, rest_tokens) = parse_tokens_recur(&rest_tokens[1..])?;
                Some((App(Box::new(term_a), Box::new(term_b)), rest_tokens))
            } else {
                None
            }
        },
        Token::Close => None,
    }
}

fn parse_tokens(tokens: &[Token]) -> Option<Term> {
    let (term, rest_tokens) = parse_tokens_recur(tokens)?;
    if rest_tokens.len() == 0 {
        Some(term) 
    } else {
        None
    }

}

//for now only works up to 9 de-bruijn, higher things could be done at some point
fn parse_term(term_string: String) -> Option<Term> {
    parse_tokens(&tokenize(term_string))
}

fn main() {
    // next todo item: solve terms that loop, but start looping later than step 1
    let max_size = 22;
    let step_limit = 100;
    let table = dp_list_terms_of_size_open(max_size, 0);
    for size in 0..=max_size {
        println!("\n\nsize: {}", size);
        let input = table[size][0].clone();
        let red_terms = reduce_list_of_terms(input, step_limit);
        let output = check_loops(red_terms, 10);
        display_output(output, step_limit);
    }
}

mod test {
    use super::*;
    
    fn t_str(s: &str) -> Term {
        parse_term(s.to_owned()).unwrap()
    }

    fn id() -> Term {
        Lambda(Box::new(Index(1)))
    }

    fn zero() -> Term {
        Lambda(Box::new(Lambda(Box::new(
            Index(1)
        ))))
    }

    fn one() -> Term {
        Lambda(Box::new(Lambda(Box::new(
            App(Box::new(Index(2)), Box::new(Index(1)))
        ))))
    }

    #[test]
    fn terms_print() {
        let id = Lambda(Box::new(Index(1)));
        let one = Lambda(Box::new(Lambda(Box::new(App(Box::new(Index(2)), Box::new(Index(1)))))));
        
        let id_str = "λ1";
        let one_str = "λλ(2)1";

        assert_eq!(print_term(&id), id_str);
        assert_eq!(print_term(&one), one_str);
    }

    #[test]
    fn terms_parse_round_trip() {
        let id = Lambda(Box::new(Index(1)));
        let one = Lambda(Box::new(Lambda(Box::new(App(Box::new(Index(2)), Box::new(Index(1)))))));

        assert_eq!(parse_term(print_term(&id)), Some(id));
        assert_eq!(parse_term(print_term(&one)), Some(one));

        let two = "λλ(2)(2)1";
        assert_eq!(print_term(&parse_term(two.to_owned()).unwrap()), two);
        let three = "λλ(2)(2)(2)1";
        assert_eq!(print_term(&parse_term(three.to_owned()).unwrap()), three);
        let plus_part = "((3)2)1";
        assert_eq!(print_term(&parse_term(plus_part.to_owned()).unwrap()), plus_part);
        let plus = "λλλλ((4)2)((3)2)1";
        assert_eq!(print_term(&parse_term(plus.to_owned()).unwrap()), plus);
    }

    #[test]
    fn term_size_test() {
        let id = Lambda(Box::new(Index(1)));
        // one = λλA21
        let one = Lambda(Box::new(Lambda(Box::new(App(Box::new(Index(2)), Box::new(Index(1)))))));
        assert_eq!(term_size(&id), 4);
        assert_eq!(term_size(&one), 11);
        // 4 lambdas -> 8, then A A42 AA321 which is 4 As -> 8
        // 42 -> 4 + 4 = 8, 321 -> 6 + 3 = 9
        // 8 + 8 + 8 + 9 = 33
        let plus_str = "λλλλ((4)2)((3)2)1";
        let plus = parse_term(plus_str.to_owned()).unwrap();
        assert_eq!(term_size(&plus), 33);
    }

    #[test]
    fn term_openness_test() {
        assert_eq!(term_openness(&id()), 0);
        assert_eq!(term_openness(&one()), 0);
        assert_eq!(term_openness(&t_str("λ3")), 2);
        assert_eq!(term_openness(&t_str("λ4")), 3);
        assert_eq!(term_openness(&t_str("(1)(λλ3)λ1")), 1);
        assert_eq!(term_openness(&t_str("((((4)5)6)7)8")), 8);
    }
    
    #[test]
    fn term_closed_test() {
        assert_eq!(is_closed(&id()), true);
        assert_eq!(is_closed(&one()), true);
        assert_eq!(is_closed(&t_str("λ3")), false);
        assert_eq!(is_closed(&t_str("λ4")), false);
        assert_eq!(is_closed(&t_str("(1)(λλ3)λ1")), false);
        assert_eq!(is_closed(&t_str("((((4)5)6)7)8")), false);
    }

    #[test]
    fn term_counting_works() {
        let correct_ans = vec![0, 0, 0, 0, 1, //0 to 4
                                         0, 1, 1, 2, 1, //5 to 9
                                         6, 5, 13, 14, 37, //10 to 12 by hand, rest by calculation
                                         44, 101, 134, 298, 431, //15 to 19
                                         883, 1361, 2736, 4405, 8574, //20 to 24
                                         14334, 27465, 47146, 89270, 156360, //25 to 29
                                         293_840, 522_913, 978_447, 1_761_907, 3_288_605, //30 to 34
                                         5_977_863, 11_148_652, 20_414_058, 38_071_898, 70_125_402, //35 to 39
                                         130_880_047, 242_222_714, 452_574_468, 840_914_719, 1_573_331_752, //40 to 44
                                         2_933_097_201, 5_495_929_096, 10_275_069_737, 19_282_848_050, 36_140_122_614, //45 to 49
                                         67_928_087_938, 127_589_648_624, 240_179_940_582, 452_010_210_830, 852_138_794_150, //50 to 54
                                         1_606_513_707_059, 3_032_924_598_421, 5_727_034_034_907, 10_826_642_256_913, 20_473_798_909_321, //55 to 59
                                         38_754_322_685_329, 73_385_837_088_228, 139_079_361_409_127, 263_693_749_320_202, 500_323_417_424_622, //60 to 64
                                        ];
        let mut calculated_ans = vec![];
        for size in 0..correct_ans.len() {
            calculated_ans.push(dp_counting_terms_of_size_open(size, 0));
        }
        assert_eq!(correct_ans, calculated_ans);

    }


    #[test]
    fn test_nf_reduce() {
        let t = t_str(&"λ(λ2)λ1");
        let (nf_t, _) = nf_reduce(&t, 10);
        let ans = t_str(&"λ1");
        assert_eq!(nf_t, ans);

        assert_eq!(nf_reduce(&t_str(&"λ(λ(2)1)1"), 10).0, t_str(&"λ(1)1"));
        assert_eq!(nf_reduce(&t_str(&"λ(λ(1)2)1"), 10).0, t_str(&"λ(1)1"));
        assert_eq!(nf_reduce(&t_str(&"λλ(λ1)λ3"), 10).0, t_str(&"λλλ3"));
        assert_eq!(nf_reduce(&t_str(&"λλ(λ3)λ1"), 10).0, t_str(&"λλ2"));

        assert_eq!(nf_reduce(&t_str(&"λ(λλ2)1"), 10).0, t_str(&"λλ2"));
        assert_eq!(nf_reduce(&t_str(&"λλ(λλ2)2"), 10).0, t_str(&"λλλ3"));
        assert_eq!(nf_reduce(&t_str(&"λ(λλ2)λ2"), 10).0, t_str(&"λλλ3"));

        let x = t_str(&"λλλ(λ(λλ3)(1)2)(1)λ4");
        let x_red_1 = nf_reduce_step(x.clone()).unwrap();
        let x_red_1_str = print_term(&x_red_1);
        let (x_red, _steps) = nf_reduce(&x, 10);
        // dbg!(steps);
        let x_red_str = print_term(&x_red);
        let y = t_str(&"λλλ(λλ(3)λ6)((1)λ4)1");
        let y_str = print_term(&y);
        let z = t_str(&"λλλλ(2)λ5");
        let z_str = print_term(&z);
        assert_eq!(x_red_1_str, y_str);
        assert_eq!(x_red_str, z_str);
        // assert_eq!(nf_reduce(t_str(&"λλλ(λ(λλ3)(1)2)(1)λ4")).0, 
        //                      t_str(&"λλλ(λλ(3)λ6)((1)λ4)1"));
    }

    #[test]
    fn test_enumerate_terms_of_size() {
        let table_to_16 = dp_list_terms_of_size_open(24, 0);
        for size in 0..=24 {
            let table_size = table_to_16[size][0].len();
            let ans = dp_counting_terms_of_size_open(size, 0);
            assert_eq!(table_size, ans.try_into().unwrap(), "size {}", size);
        }
    }
    /*
    functions to write:
        print term in a human readable way instead of de bruijn
        reduce terms, separate into holdouts and non-holdouts, etc. 
    tests still to write:
        substitute?
        whnf reduction?
     */
}