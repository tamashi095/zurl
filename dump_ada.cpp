// Dumps ada::parse<ada::url_aggregator> results for a URL list file.
// Usage: dump_ada <file>          -> one line per URL: the href, or "INVALID".
//        dump_ada resolve <file>  -> TSV of hex(base)\thex(input) per line;
//                                    prints "href\torigin", "INVALID", or
//                                    "BASE_INVALID" per line.
#include "ada.h"

#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

static int hexval(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static std::string unhex(std::string_view h) {
  std::string r;
  r.reserve(h.size() / 2);
  for (size_t i = 0; i + 1 < h.size(); i += 2) {
    int hi = hexval(h[i]), lo = hexval(h[i + 1]);
    if (hi < 0 || lo < 0) break;
    r.push_back((char)((hi << 4) | lo));
  }
  return r;
}

static void append_result(std::string& outbuf, std::string_view base,
                          std::string_view input) {
  if (!base.empty()) {
    auto b = ada::parse<ada::url_aggregator>(base);
    if (!b) {
      outbuf.append("BASE_INVALID\n");
      return;
    }
    auto url = ada::parse<ada::url_aggregator>(input, &*b);
    if (url) {
      std::string_view href = url->get_href();
      const std::string origin = url->get_origin();
      outbuf.append(href.data(), href.size());
      outbuf.push_back('\t');
      outbuf.append(origin.data(), origin.size());
    } else {
      outbuf.append("INVALID");
    }
    outbuf.push_back('\n');
    return;
  }
  auto url = ada::parse<ada::url_aggregator>(input);
  if (url) {
    std::string_view href = url->get_href();
    const std::string origin = url->get_origin();
    outbuf.append(href.data(), href.size());
    outbuf.push_back('\t');
    outbuf.append(origin.data(), origin.size());
  } else {
    outbuf.append("INVALID");
  }
  outbuf.push_back('\n');
}

int main(int argc, char** argv) {
  bool resolve_mode = argc > 2 && std::strcmp(argv[1], "resolve") == 0;
  const char* path = argc > 1 ? (resolve_mode ? argv[2] : argv[1]) : nullptr;
  if (!path) {
    fprintf(stderr, "usage: dump_ada [resolve] <file>\n");
    return 1;
  }
  FILE* f = fopen(path, "rb");
  if (!f) {
    perror("fopen");
    return 1;
  }
  fseek(f, 0, SEEK_END);
  long size = ftell(f);
  fseek(f, 0, SEEK_SET);
  std::string data;
  data.resize(size);
  if (fread(data.data(), 1, size, f) != (size_t)size) {
    perror("fread");
    return 1;
  }
  fclose(f);

  std::vector<std::string_view> lines;
  size_t start = 0;
  for (size_t i = 0; i <= data.size(); i++) {
    if (i == data.size() || data[i] == '\n') {
      std::string_view v(data.data() + start, i - start);
      if (resolve_mode) {
        if (!v.empty() && v.back() == '\r') v.remove_suffix(1);
      } else {
        while (!v.empty() && std::isspace((unsigned char)v.back())) v.remove_suffix(1);
        while (!v.empty() && std::isspace((unsigned char)v.front())) v.remove_prefix(1);
      }
      if (!v.empty()) lines.push_back(v);
      start = i + 1;
    }
  }

  std::string outbuf;
  outbuf.reserve(1 << 20);
  for (std::string_view line : lines) {
    if (resolve_mode) {
      size_t tab = line.find('\t');
      std::string base = unhex(line.substr(0, tab));
      std::string input = tab == std::string_view::npos ? unhex("") : unhex(line.substr(tab + 1));
      append_result(outbuf, base, input);
    } else {
      auto url = ada::parse<ada::url_aggregator>(line);
      if (url) {
        std::string_view href = url->get_href();
        outbuf.append(href.data(), href.size());
      } else {
        outbuf.append("INVALID");
      }
      outbuf.push_back('\n');
    }
    if (outbuf.size() > (1 << 19)) {
      fwrite(outbuf.data(), 1, outbuf.size(), stdout);
      outbuf.clear();
    }
  }
  fwrite(outbuf.data(), 1, outbuf.size(), stdout);
  return 0;
}
