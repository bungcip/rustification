/**
 * @file FloatingLexer.h
 * @brief Declares the matchFloatingLiteral function for lexing floating-point
 * literals.
 */

#ifndef FloatingLexer_hpp
#define FloatingLexer_hpp

#include <cstring>
#include <string>

/**
 * @brief Matches a floating-point literal at the given prefix.
 * @param prefix A pointer to the beginning of the string to match.
 * @return The matched floating-point literal.
 */
std::string matchFloatingLiteral(const char * prefix);

#endif /* FloatingLexer_hpp */
