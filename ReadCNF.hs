module ReadCNF where

import DIMACS
import Text.Parsec (char, oneOf, (<|>), many, many1, space, spaces, anyChar, manyTill, string, newline)
import Text.Parsec.Prim (skipMany)
import Text.Parsec.String (Parser)
import qualified Debug.Trace as D


natural :: Parser Int
natural = do
    n <- oneOf ['1'..'9']
    m <- many  (oneOf ['0'..'9'])
    return (read (n : m))

parseNotLiteral :: Parser Literal
parseNotLiteral = do {
                     char '-';
                     n <- natural;
                     return (Not (Var n));
                     }

parseNormalLiteral :: Parser Literal
parseNormalLiteral = do {
                        n <- natural;
                        return (Normal (Var n));
                        }

parseLiteral :: Parser Literal
parseLiteral = parseNotLiteral <|> parseNormalLiteral

parseEOL :: Parser Char
parseEOL = do {
              space;
              char '0';
              }

parseLiterals :: Parser [Literal]
parseLiterals = do {
                   spaces;
                   l <- parseLiteral;
                   spaces;
                   ls <- parseLiterals;
                   return (l:ls);
                   }
                   <|> do {
                          char '0';
                          return [];
                          }

parseClause :: Parser　Clause
parseClause = do {
                 spaces;
                 ls <-parseLiterals;
                 newline;
                 case (length ls) of
                   0 -> return EmptyClause
                   1 -> return $ UnitClause (head ls)
                   _ -> return $ Clause ls
                   }


parseCNF :: Parser CNF
parseCNF = do {
              cs <- many1 parseClause;
              return (CNF cs);
              }

parseComment :: Parser String
parseComment = do {
                  char 'c';
                  comment <- (manyTill anyChar newline);
                  return comment
                  }


dprint :: (Show a) => a -> a
dprint a = (D.trace (show a) a)

parseHeader :: Parser Header
parseHeader = do {
                 char 'p';
                 spaces;
                 string "cnf";
                 spaces;
                 vc <- natural;
                 spaces;
                 cc <- natural;
                 (manyTill anyChar newline);
                 return (Header vc cc);
                 }


parseDIMACS :: Parser DIMACS
parseDIMACS = do {
                 skipMany parseComment;
                 header <- parseHeader;
                 cnf <- parseCNF;
                 case header of
                   (Header vc cc) -> return DIMACS {
                                                   _variableCount = vc
                                                   ,_clauseCount = cc
                                                   ,_cnf = cnf};
                                                   }

