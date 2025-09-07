/**
 * @file AstExporter.hpp
 * @brief Declares the process function for exporting Clang ASTs.
 */

#ifndef AstExporter_hpp
#define AstExporter_hpp

#include <string>
#include <unordered_map>
#include <vector>

using Outputs = std::unordered_map<std::string, std::vector<uint8_t>>;

/**
 * @brief Processes the command-line arguments and exports the Clang ASTs.
 * @param argc The number of command-line arguments.
 * @param argv The command-line arguments.
 * @param result A pointer to an integer that will be set to the result of the
 * operation.
 * @return A map of file paths to their corresponding CBOR-encoded ASTs.
 */
Outputs process(int argc, const char *argv[], int *result);

#endif /* AstExporter_hpp */
