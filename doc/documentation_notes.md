# Notes on compiling documentation

Currently, to setup Sage to be able to compile the documentation, I am using:
```bash
sage -pip install sphinx sphinx_rtd_theme myst-parser
```

Then from the `doc/` subdirectory I am running the command

```bash
make html
```

This will create html documentation which is contained in the directory `doc/build/html/`.

## Notes on ReStructured Text

References on ReStructured Text (RST), which is used in Python comments:

* [https://docs.open-mpi.org/en/v5.0.x/developers/rst-for-markdown-expats.html](ReStructured Text for those who know Markdown)
