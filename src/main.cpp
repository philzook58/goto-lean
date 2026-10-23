#include "printer.h"
#include <goto-programs/goto_model.h>
#include <goto-programs/read_goto_binary.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/message.h>
#include <util/version.h>
#include <filesystem>
#include <cstdio>
#include <cstring>
#include <unistd.h>
#include <vector>
#include <fstream>
#include <iostream>
#include <stdexcept>

int main(int argc, char **argv) {
  try {
    const std::string help = "Usage: goto-lean INPUT.gb --function NAME -o OUTPUT.lean\n"
      "Print a GOTO entry and reachable direct callees as Lean (translation does not verify it).\n";
    if (argc == 2 && std::string(argv[1]) == "--version") {
      std::cout << "goto-lean 0.1.0; CBMC " << CBMC_VERSION << " (" << GOTO_LEAN_CBMC_REV << ")\n";
      return 0;
    }
    if (argc == 1 || (argc == 2 && std::string(argv[1]) == "--help")) {
      std::cout << help; return argc == 1 ? 2 : 0;
    }
    std::string input = argv[1], function, output;
    for (int i = 2; i < argc; ++i) {
      std::string key = argv[i];
      if (++i == argc) throw std::runtime_error("option has no value: " + key);
      if (key == "--function" && function.empty()) function = argv[i];
      else if (key == "-o" && output.empty()) output = argv[i];
      else throw std::runtime_error("unknown or repeated option: " + key);
    }
    if (function.empty() || output.empty()) throw std::runtime_error(help);
    if (std::filesystem::absolute(input).lexically_normal() ==
        std::filesystem::absolute(output).lexically_normal())
      throw std::runtime_error("input and output must differ");
    stream_message_handlert messages(std::cerr);
    cmdlinet defaults;
    config.set(defaults);
    auto model = read_goto_binary(input, messages);
    if (!model) throw std::runtime_error("cannot read GOTO binary: " + input);
    config.set_from_symbol_table(model->symbol_table);
    const auto text = print_lean(*model, function);
    // Publish only after validation/translation, using a same-directory temporary file.
    std::vector<char> pattern(output.begin(), output.end());
    const std::string suffix = ".tmp.XXXXXX";
    pattern.insert(pattern.end(), suffix.begin(), suffix.end());
    pattern.push_back('\0');
    const int fd = mkstemp(pattern.data());
    if (fd < 0) throw std::runtime_error("cannot create output: " + std::string(std::strerror(errno)));
    const std::string temp(pattern.data());
    FILE *stream = fdopen(fd, "wb");
    if (!stream) {
      close(fd); std::filesystem::remove(temp);
      throw std::runtime_error("cannot open output stream");
    }
    const bool written = std::fwrite(text.data(), 1, text.size(), stream) == text.size();
    const bool closed = std::fclose(stream) == 0;
    try {
      if (!written || !closed) throw std::runtime_error("cannot write output");
      std::filesystem::rename(temp, output);
    } catch (...) {
      std::error_code ignored;
      std::filesystem::remove(temp, ignored);
      throw;
    }
    return 0;
  } catch (const std::exception &error) {
    std::cerr << "goto-lean: " << error.what() << '\n';
    return 2;
  } catch (const std::string &error) {
    std::cerr << "goto-lean: " << error << '\n'; return 2;
  }
}
