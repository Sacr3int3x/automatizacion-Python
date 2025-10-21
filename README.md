MaintenanceApp — Preventive Maintenance Manager

This desktop tool automates and simplifies preventive maintenance workflows for technical sites. Built with CustomTkinter, it combines a clear UI and backend automation for managing station data, generating structured PDF reports, and handling duplicate image files.
It supports persistent user preferences, background threading for non-blocking tasks, and integrates file hashing for fast duplicate detection.

Key modules include:
  - MaintenanceApp class: Core application controller, handling UI setup, state persistence, and task orchestration.
  - File Hashing System: Uses MD5 signatures and JSON cache for efficient duplicate image detection.
  - PDF Reporting: Automatically compiles and previews detailed maintenance reports.
  - Station Management: Imports and processes station data from Excel workbooks.
  - Image Review Interface: Enables manual review and deletion of redundant photos safely.
  - Main dependencies: customtkinter, pandas, hashlib, json, os, subprocess, threading, reportlab.
