/**
 * @file ExportResult.hpp
 * @brief Declares the ExportResult struct for passing AST export results from
 * C++ to Rust.
 */

#ifndef ExportResult_hpp
#define ExportResult_hpp

#include <algorithm>
#include <cstddef>
#include <cstdint>

/**
 * @struct ExportResult
 * @brief A struct that is used to pass the results of the AST export from C++
 * to Rust.
 */
struct ExportResult {
    /// The number of entries in the result.
    std::size_t entries;
    /// The names of the files.
    char **names;
    /// The CBOR-encoded ASTs.
    std::uint8_t **bytes;
    /// The sizes of the CBOR-encoded ASTs.
    std::size_t *sizes;

    /**
     * @brief Constructs a new ExportResult object.
     */
    ExportResult();
    ExportResult(ExportResult const &) = delete;
    ExportResult &operator=(ExportResult const &) = delete;

    /**
     * @brief Destroys the ExportResult object.
     */
    ~ExportResult();

    /**
     * @brief Resizes the result to hold n entries.
     * @param n The new number of entries.
     */
    void resize(std::size_t n);

  private:
    void deallocate();
};

#endif /* ExportResult_hpp */
